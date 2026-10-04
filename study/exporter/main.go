// Small reproducible wrappers around gnark v0.14.0 public circuit code.
package main

import (
    "encoding/json"
    "fmt"
    "math/big"
    "math/rand"
    "os"
    "path/filepath"
    "runtime"
    "time"
    edid "github.com/consensys/gnark-crypto/ecc/twistededwards"
    ednative "github.com/consensys/gnark-crypto/ecc/bn254/twistededwards"
    ed "github.com/consensys/gnark/std/algebra/native/twistededwards"
    "github.com/consensys/gnark/constraint/solver"

    "github.com/consensys/gnark-crypto/ecc"
    "github.com/consensys/gnark-crypto/ecc/bn254/fr"
    native "github.com/consensys/gnark-crypto/ecc/bn254/fr/mimc"
    "github.com/consensys/gnark/constraint"
    csbn "github.com/consensys/gnark/constraint/bn254"
    "github.com/consensys/gnark/examples/cubic"
    "github.com/consensys/gnark/frontend"
    "github.com/consensys/gnark/frontend/cs/r1cs"
    mimc "github.com/consensys/gnark/std/hash/mimc"
    "github.com/consensys/gnark/std/math/bits"
)

type BitCircuit struct { X frontend.Variable `gnark:",public"`; N int `gnark:"-"` }
func (c *BitCircuit) Define(api frontend.API) error {
    bits.ToBinary(api, c.X, bits.WithNbDigits(c.N))
    return nil
}

type ZeroCircuit struct { X frontend.Variable `gnark:",public"`; Y frontend.Variable }
func (c *ZeroCircuit) Define(api frontend.API) error {
    api.AssertIsEqual(c.Y, api.IsZero(c.X))
    return nil
}

type HashCircuit struct { Digest frontend.Variable `gnark:",public"`; Data []frontend.Variable }
func (c *HashCircuit) Define(api frontend.API) error {
    h, err := mimc.NewMiMC(api); if err != nil { return err }
    h.Write(c.Data...)
    api.AssertIsEqual(c.Digest, h.Sum())
    return nil
}

type ChainCircuit struct { X frontend.Variable `gnark:",public"`; N int `gnark:"-"` }
func (c *ChainCircuit) Define(api frontend.API) error {
    x := c.X
    for i:=0;i<c.N;i++ { h,e:=mimc.NewMiMC(api); if e!=nil{return e}; h.Write(x); x=h.Sum() }
    return nil
}
type ScalarCircuit struct { S frontend.Variable `gnark:",public"`; QX,QY frontend.Variable }
func (c *ScalarCircuit) Define(api frontend.API) error {
    curve,err:=ed.NewEdCurve(api,edid.BN254); if err!=nil{return err}
    q:=curve.ScalarMul(ed.Point{X:curve.Params().Base[0],Y:curve.Params().Base[1]},c.S)
    api.AssertIsEqual(q.X,c.QX); api.AssertIsEqual(q.Y,c.QY)
    return nil
}
func zeroHint(_ *big.Int,_ []*big.Int,outs []*big.Int) error {
    for _,x:=range outs{x.SetInt64(0)};return nil
}

type Term struct { Wire int `json:"wire"`; Coeff string `json:"coefficient"` }
type Row struct { L []Term `json:"l"`; R []Term `json:"r"`; O []Term `json:"o"` }
type Export struct {
    Name string `json:"name"`
    Source string `json:"source"`
    Scope string `json:"scope"`
    GoVersion string `json:"go_version"`
    Gnark string `json:"gnark"`
    Crypto string `json:"gnark_crypto"`
    Prime string `json:"prime"`
    Names []string `json:"names"`
    Values []string `json:"values"`
    Fixed []int `json:"fixed"`
    Targets []int `json:"targets"`
    Rows []Row `json:"rows"`
    Public []string `json:"public_names"`
    Secret []string `json:"secret_names"`
    Solved bool `json:"gnark_solve_passed"`
    CompileSeconds float64 `json:"compile_seconds"`
    SolveSeconds float64 `json:"solve_seconds"`
}

func export(name, source, scope string, circuit, assignment frontend.Circuit, targetNames []string, options ...solver.Option) error {
    started:=time.Now()
    generic, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, circuit)
    if err != nil { return err }
    compileSeconds:=time.Since(started).Seconds()
    cs := generic.(*csbn.R1CS)
    witness, err := frontend.NewWitness(assignment, ecc.BN254.ScalarField()); if err != nil { return err }
    started=time.Now()
    raw, err := cs.Solve(witness,options...); if err != nil { return err }
    solution := raw.(*csbn.R1CSSolution)
    solveSeconds:=time.Since(started).Seconds()
    e := Export{CompileSeconds:compileSeconds,SolveSeconds:solveSeconds,Name:name, Source:source, Scope:scope, GoVersion:runtime.Version(), Gnark:"v0.14.0", Crypto:"v0.19.0", Prime:fr.Modulus().String(), Public:cs.Public, Secret:cs.Secret, Solved:true}
    for i := range solution.W {
        var value big.Int; solution.W[i].BigInt(&value)
        e.Values = append(e.Values, value.String())
        var wireName string
        if i < len(cs.Public) { wireName = cs.Public[i]; e.Fixed = append(e.Fixed, i)
        } else if i < len(cs.Public)+len(cs.Secret) { wireName = cs.Secret[i-len(cs.Public)]
        } else { wireName = fmt.Sprintf("internal_%d", i) }
        e.Names = append(e.Names, wireName)
        for _, t := range targetNames { if wireName == t { e.Targets = append(e.Targets, i) } }
    }
    terms := func(expression constraint.LinearExpression) []Term {
        result := []Term{}
        for _, t := range expression {
            index := t.WireID(); if t.IsConstant() { index = -1 }
            result = append(result, Term{Wire:index, Coeff:cs.ToBigInt(cs.GetCoefficient(t.CoeffID())).String()})
        }
        return result
    }
    for _, row := range cs.GetR1Cs() { e.Rows = append(e.Rows, Row{terms(row.L),terms(row.R),terms(row.O)}) }
    data, err := json.Marshal(e); if err != nil { return err }
    if err := os.WriteFile(filepath.Join("..","exports",name+".json"), append(data,'\n'),0644); err != nil { return err }
    fmt.Printf("EXPORTED %s: %d wires, %d constraints, fixed=%v, targets=%v\n",name,len(e.Values),len(e.Rows),e.Fixed,e.Targets)
    return nil
}

func main() {
    if len(os.Args)>1 && os.Args[1]=="sweep" { sweep(); return }
    if err := os.MkdirAll("../exports",0755); err != nil { panic(err) }
    must := func(err error) { if err != nil { panic(err) } }
    cubicSource := "https://github.com/Consensys/gnark/blob/v0.14.0/examples/cubic/cubic.go"
    must(export("cubic_regular",cubicSource,"Fix public Y=35; target private x",&cubic.Circuit{},&cubic.Circuit{X:3,Y:35},[]string{"x"}))
    // Critical input of the SAME upstream cubic: 3*x^2+1=0, not a mutated circuit.
    p := fr.Modulus()
    criticalSquared := new(big.Int).Neg(new(big.Int).ModInverse(big.NewInt(3),p))
    criticalSquared.Mod(criticalSquared,p)
    critical := new(big.Int).ModSqrt(criticalSquared,p)
    if critical == nil { panic("No critical point over this field") }
    y := new(big.Int).Exp(critical,big.NewInt(3),p)
    y.Add(y,critical).Add(y,big.NewInt(5)).Mod(y,p)
    must(export("cubic_critical",cubicSource,"Fix public Y at a critical value; target private x",&cubic.Circuit{},&cubic.Circuit{X:critical,Y:y},[]string{"x"}))
    for _, n := range []int{8,32} {
        must(export(fmt.Sprintf("bits_%d",n),"https://github.com/Consensys/gnark/blob/v0.14.0/std/math/bits/conversion_binary.go","Fix public X=173; retain all internal bit coordinates",&BitCircuit{N:n},&BitCircuit{X:173,N:n},nil))
    }
    for _, x := range []int{0,7} {
        y := 0; if x==0 { y=1 }
        must(export(fmt.Sprintf("iszero_%d",x),"https://github.com/Consensys/gnark/blob/v0.14.0/frontend/cs/r1cs/api.go","Fix public X; target Y; inverse-hint freedom is not itself a target bug",&ZeroCircuit{},&ZeroCircuit{X:x,Y:y},[]string{"Y"}))
    }
    for _, n := range []int{1,2} {
        data := make([]frontend.Variable,n)
        h := native.NewMiMC()
        for i := range data {
            data[i] = i+7
            var element fr.Element; element.SetUint64(uint64(i+7)); b := element.Bytes()
            if _,err := h.Write(b[:]); err != nil { panic(err) }
        }
        digest := new(big.Int).SetBytes(h.Sum(nil))
        must(export(fmt.Sprintf("mimc_%d",n),"https://github.com/Consensys/gnark/blob/v0.14.0/std/hash/mimc/mimc.go","Fix public digest; inspect private preimage directions, not a preimage-uniqueness security specification",&HashCircuit{Data:make([]frontend.Variable,n)},&HashCircuit{Digest:digest,Data:data},[]string{"Data_0","Data_1"}))
    }
    for _,n:=range []int{3,20,60,120,200} {
      must(export(fmt.Sprintf("chain_%d",n),"gnark v0.14.0 std/hash/mimc","Public X=7; all non-fixed wires are analysis targets, not pinned outputs",&ChainCircuit{N:n},&ChainCircuit{X:7,N:n},nil))
    }
    base:=ednative.GetEdwardsCurve().Base
    hints:=ed.GetHints()
    for _,scalar:=range []int64{0,1,12345,54321} {
      var q ednative.PointAffine; q.ScalarMultiplication(&base,big.NewInt(scalar))
      var qx,qy big.Int;q.X.BigInt(&qx);q.Y.BigInt(&qy)
      assign:=&ScalarCircuit{S:scalar,QX:&qx,QY:&qy}
      must(export(fmt.Sprintf("scalar_%d_honest",scalar),"gnark v0.14.0 native/twistededwards ScalarMul","Fix S; target unconditioned QX,QY",&ScalarCircuit{},assign,[]string{"QX","QY"}))
      must(export(fmt.Sprintf("scalar_%d_zero_decomp",scalar),"gnark v0.14.0 native/twistededwards ScalarMul","Same relation and statement; halfGCD hint outputs zeroed",&ScalarCircuit{},assign,[]string{"QX","QY"},solver.OverrideHint(solver.GetHintID(hints[0]),zeroHint)))
      var forged ednative.PointAffine;forged.ScalarMultiplication(&base,big.NewInt(scalar+1))
      var fx,fy big.Int;forged.X.BigInt(&fx);forged.Y.BigInt(&fy)
      forgedHint:=func(_ *big.Int,_ []*big.Int,outs []*big.Int)error{outs[0].Set(&fx);outs[1].Set(&fy);return nil}
      must(export(fmt.Sprintf("scalar_%d_forged",scalar),"gnark v0.14.0 native/twistededwards ScalarMul","Same relation and S; Q is [S+1]G, halfGCD zero, scalarMulHint overridden",&ScalarCircuit{},&ScalarCircuit{S:scalar,QX:&fx,QY:&fy},[]string{"QX","QY"},solver.OverrideHint(solver.GetHintID(hints[0]),zeroHint),solver.OverrideHint(solver.GetHintID(hints[1]),forgedHint)))
    }

}

func sweep() {
    if err:=os.MkdirAll("../exports",0755);err!=nil{panic(err)}
    scalar:=int64(12345);base:=ednative.GetEdwardsCurve().Base
    var q ednative.PointAffine;q.ScalarMultiplication(&base,big.NewInt(scalar))
    var qx,qy big.Int;q.X.BigInt(&qx);q.Y.BigInt(&qy)
    hints:=ed.GetHints(); rng:=rand.New(rand.NewSource(20261003))
    results:=[]map[string]interface{}{}
    for variant:=0;variant<20;variant++ {
      fx,fy:=new(big.Int).Set(&qx),new(big.Int).Set(&qy)
      var options []solver.Option
      label:="honest"
      if variant==1 || variant==11 || variant>=12 {
         options=append(options,solver.OverrideHint(solver.GetHintID(hints[0]),zeroHint));label="decomposition_zero"
      }
      if variant>=2 && variant<=6 {
        idx:=variant-2;label=fmt.Sprintf("decomposition_output_%d_zero",idx)
        if variant==6 {label="decomposition_sign_flip"}
        fn:=func(mod *big.Int,inputs,outputs []*big.Int)error{
           if err:=hints[0](mod,inputs,outputs);err!=nil{return err}
           if idx<4 {outputs[idx].SetInt64(0)} else {outputs[2].Sub(big.NewInt(1),outputs[2])}
           return nil
        }
        options=append(options,solver.OverrideHint(solver.GetHintID(hints[0]),fn))
      }
      switch variant {
      case 7:fx.SetInt64(0);fy.SetInt64(0);label="point_zero"
      case 8:fx.SetInt64(0);label="point_x_zero"
      case 9:fy.SetInt64(0);label="point_y_zero"
      case 10:fx.SetInt64(0);fy.SetInt64(1);label="point_identity"
      case 11:fx.SetInt64(0);fy.SetInt64(0);label="both_hints_zero"
      }
      if variant>=12 {fx.Rand(rng,fr.Modulus());fy.Rand(rng,fr.Modulus());label=fmt.Sprintf("random_point_zero_decomposition_%d",variant-12)}
      if variant>=7 {
        fn:=func(_ *big.Int,_ []*big.Int,outputs []*big.Int)error{outputs[0].Set(fx);outputs[1].Set(fy);return nil}
        options=append(options,solver.OverrideHint(solver.GetHintID(hints[1]),fn))
      }
      name:=fmt.Sprintf("sweep_%02d_%s",variant,label);start:=time.Now()
      err:=export(name,"gnark v0.14.0 native/twistededwards ScalarMul","Same S=12345; targeted hint mutations; explicit unconditioned QX,QY",&ScalarCircuit{},&ScalarCircuit{S:scalar,QX:fx,QY:fy},[]string{"QX","QY"},options...)
      result:=map[string]interface{}{"name":name,"variant":variant,"label":label,"scalar":scalar,"compile_solve_export_seconds":time.Since(start).Seconds(),"witness_generated":err==nil}
      if err!=nil {result["solver_error"]=err.Error();fmt.Printf("REJECTED %s: %s\n",name,err.Error())}
      results=append(results,result)
    }
    data,err:=json.MarshalIndent(results,"","  ");if err!=nil{panic(err)}
    if err:=os.WriteFile("../results/witness-sweep-generation.json",append(data,'\n'),0644);err!=nil{panic(err)}
}
