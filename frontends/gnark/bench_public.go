package main

// Public scaling family for the Jacobian determinacy benchmark. Unlike the
// backend circuits, this file depends only on gnark's standard library, so the
// exported R1CS/witness artifacts and this source can ship with the paper.

import (
	"bytes"
	"crypto/rand"
	"os"
	"strconv"

	tedwards "github.com/consensys/gnark-crypto/ecc/twistededwards"
	ceddsa "github.com/consensys/gnark-crypto/signature/eddsa"

	cmimc "github.com/consensys/gnark-crypto/ecc/bn254/fr/mimc"
	"github.com/consensys/gnark-crypto/accumulator/merkletree"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/accumulator/merkle"
	"github.com/consensys/gnark/std/algebra/native/twistededwards"
	"github.com/consensys/gnark/std/hash/mimc"
	"github.com/consensys/gnark/std/hash/sha2"
	"github.com/consensys/gnark/std/math/uints"
	"github.com/consensys/gnark/std/signature/eddsa"
)

// benchEnvInt mirrors envi from the backend-tagged file; duplicated here so the
// public benchmark builds without the backend tag (and its client deps).
func benchEnvInt(key string, def int) int {
	if s := os.Getenv(key); s != "" {
		if v, err := strconv.Atoi(s); err == nil {
			return v
		}
	}
	return def
}

// MiMCChain hashes the single public input X through N chained MiMC
// permutations. The final digest is deliberately left unpinned (the
// PoseidonWit pattern): the solver fills every internal round wire from X
// alone, so the ground truth for the determinacy diagnostic is that every
// internal wire comes back DETERMINED. N scales the constraint count
// linearly, giving a public benchmark family spanning ~1k to ~60k+
// constraints via GNARK_MIMC.
type MiMCChain struct {
	X frontend.Variable `gnark:",public"`
	N int
}

func (c *MiMCChain) Define(api frontend.API) error {
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	cur := c.X
	for i := 0; i < c.N; i++ {
		h.Reset()
		h.Write(cur)
		cur = h.Sum()
	}
	_ = cur
	return nil
}

// MiMCTree reduces 2^K public leaves pairwise to a single root (left
// unpinned), a wide tree-reduction topology as opposed to MiMCChain's path.
type MiMCTree struct {
	Leaves []frontend.Variable `gnark:",public"`
}

func (c *MiMCTree) Define(api frontend.API) error {
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	level := c.Leaves
	for len(level) > 1 {
		next := make([]frontend.Variable, len(level)/2)
		for i := range next {
			h.Reset()
			h.Write(level[2*i], level[2*i+1])
			next[i] = h.Sum()
		}
		level = next
	}
	_ = level[0]
	return nil
}

// MerklePath verifies a Merkle inclusion proof (gnark std accumulator) —
// a path topology with index-bit selectors, i.e. guarded structure.
type MerklePath struct {
	Leaf frontend.Variable  `gnark:",public"`
	M    merkle.MerkleProof `gnark:",public"`
}

func (c *MerklePath) Define(api frontend.API) error {
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	c.M.VerifyProof(api, &h, c.Leaf)
	return nil
}

// EdDSAVerify verifies one EdDSA signature (gnark std) — mixed topology:
// twisted-Edwards double-and-add, bit decompositions, and MiMC.
type EdDSAVerify struct {
	PublicKey eddsa.PublicKey   `gnark:",public"`
	Signature eddsa.Signature   `gnark:",public"`
	Message   frontend.Variable `gnark:",public"`
}

func (c *EdDSAVerify) Define(api frontend.API) error {
	curve, err := twistededwards.NewEdCurve(api, tedwards.BN254)
	if err != nil {
		return err
	}
	h, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	return eddsa.Verify(curve, c.Signature, c.Message, c.PublicKey, &h)
}

// SHA256Block hashes a fixed 64-byte message (gnark std sha2) — a bitwise
// u8/u32 topology unlike any of the field-native families above.
type SHA256Block struct {
	In [64]uints.U8 `gnark:",public"`
}

func (c *SHA256Block) Define(api frontend.API) error {
	h, err := sha2.New(api)
	if err != nil {
		return err
	}
	h.Write(c.In[:])
	_ = h.Sum()
	return nil
}

func merkleAssignment() frontend.Circuit {
	k := benchEnvInt("GNARK_MERKLE_K", 5) // 2^k leaves, proof has k+1 path nodes
	nLeaves := uint64(1) << k
	segSize := 32
	var buf bytes.Buffer
	for i := uint64(0); i < nLeaves; i++ {
		seg := make([]byte, segSize)
		seg[0] = 0 // keep each segment below the BN254 scalar modulus
		seg[31] = byte(i + 1)
		seg[30] = byte(i >> 8)
		buf.Write(seg)
	}
	idx := uint64(1)
	hGo := cmimc.NewMiMC()
	root, proofSet, _, err := merkletree.BuildReaderProof(&buf, hGo, segSize, idx)
	if err != nil {
		panic(err)
	}
	a := &MerklePath{Leaf: idx}
	a.M.RootHash = root
	a.M.Path = make([]frontend.Variable, len(proofSet))
	for i, p := range proofSet {
		a.M.Path[i] = p
	}
	return a
}

func eddsaAssignment() frontend.Circuit {
	priv, err := ceddsa.New(tedwards.BN254, rand.Reader)
	if err != nil {
		panic(err)
	}
	msg := make([]byte, 32)
	msg[31] = 42 // fixed small message, valid BN254 fr element
	hGo := cmimc.NewMiMC()
	sig, err := priv.Sign(msg, hGo)
	if err != nil {
		panic(err)
	}
	a := &EdDSAVerify{Message: msg}
	a.PublicKey.Assign(tedwards.BN254, priv.Public().Bytes())
	a.Signature.Assign(tedwards.BN254, sig)
	return a
}

func init() {
	extra["mimcchain"] = func() frontend.Circuit {
		return &MiMCChain{N: benchEnvInt("GNARK_MIMC", 3)}
	}
	extraAssign["mimcchain"] = func() frontend.Circuit {
		return &MiMCChain{X: 3, N: benchEnvInt("GNARK_MIMC", 3)}
	}
	extra["mimctree"] = func() frontend.Circuit {
		k := benchEnvInt("GNARK_TREE_K", 6)
		return &MiMCTree{Leaves: make([]frontend.Variable, 1<<k)}
	}
	extraAssign["mimctree"] = func() frontend.Circuit {
		k := benchEnvInt("GNARK_TREE_K", 6)
		leaves := make([]frontend.Variable, 1<<k)
		for i := range leaves {
			leaves[i] = i + 1
		}
		return &MiMCTree{Leaves: leaves}
	}
	extra["merklepath"] = func() frontend.Circuit {
		k := benchEnvInt("GNARK_MERKLE_K", 5)
		c := &MerklePath{}
		c.M.Path = make([]frontend.Variable, k+1)
		return c
	}
	extraAssign["merklepath"] = merkleAssignment
	extra["eddsaverify"] = func() frontend.Circuit { return &EdDSAVerify{} }
	extraAssign["eddsaverify"] = eddsaAssignment
	extra["sha256block"] = func() frontend.Circuit { return &SHA256Block{} }
	extraAssign["sha256block"] = func() frontend.Circuit {
		a := &SHA256Block{}
		for i := range a.In {
			a.In[i] = uints.NewU8(byte(i))
		}
		return a
	}
}
