include "CDPC.dfy"
include "../Arithmetic/Rationals.dfy"

include "../Collections/Set.dfy"
include "../Collections/Map.dfy"

ghost function CDPCThresholdsModel(thresholds:CDPCThresholds<Rational>):CDPCThresholds<real>
{
  CDPCThresholds(thresholds.privateLower.Model(), thresholds.privateUpper.Model(),
    thresholds.fitnessLower.Model(), thresholds.fitnessUpper.Model())
}

// Executable verifier input with atomic question labels and stored thresholds.
datatype CDPCInstance<Q(==)> = CDPCInstance(questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>,
  multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>, thresholds:CDPCThresholds<Rational>)
{
  ghost function Model():CDPCModel<Q>
  {
    CDPCModel(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
      CDPCThresholdsModel(thresholds))
  }

  ghost function Size(weight:Q -> nat):nat
  {
    5+questions.Size(weight)+fitness.Size(weight, BoolBits, BoolBits)+
      multiplicity.Size(weight, BoolBits, NatBits)+privateQuestions.Size(weight)+CDPCThresholdsBits(thresholds)
  }

  ghost function {:opaque} SizeBound(weight:Q -> nat):(size:nat)
    ensures questions.SizeBound(weight) <= size && privateQuestions.SizeBound(weight) <= size
    ensures fitness.SizeBound(weight, BoolBits, BoolBits) <= size
    ensures multiplicity.SizeBound(weight, BoolBits, NatBits) <= size && CDPCThresholdsBits(thresholds) <= size
    ensures Size(weight) <= size
  {
    5+questions.SizeBound(weight)+fitness.SizeBound(weight, BoolBits, BoolBits)+
      multiplicity.SizeBound(weight, BoolBits, NatBits)+privateQuestions.SizeBound(weight)+CDPCThresholdsBits(thresholds)
  }
}

// The compound-label representation still needs its pending label adapter.
datatype CDPCSetInstance<T(==)> = CDPCSetInstance(questions:SetSet<T>, fitness:Map_MapSet_T<T, bool, bool>,
  multiplicity:Map_MapSet_T<T, bool, nat>, privateQuestions:SetSet<T>, thresholds:CDPCThresholds<Rational>)
{
  ghost function Size(weight:T -> nat):nat
  {
    5+questions.Size(weight)+fitness.Size(weight, BoolBits, BoolBits)+
      multiplicity.Size(weight, BoolBits, NatBits)+privateQuestions.Size(weight)+CDPCThresholdsBits(thresholds)
  }

  ghost function {:opaque} SizeBound(weight:T -> nat):(size:nat)
    ensures questions.SizeBound(weight) <= size && privateQuestions.SizeBound(weight) <= size
    ensures fitness.SizeBound(weight, BoolBits, BoolBits) <= size
    ensures multiplicity.SizeBound(weight, BoolBits, NatBits) <= size && CDPCThresholdsBits(thresholds) <= size
    ensures Size(weight) <= size
  {
    5+questions.SizeBound(weight)+fitness.SizeBound(weight, BoolBits, BoolBits)+
      multiplicity.SizeBound(weight, BoolBits, NatBits)+privateQuestions.SizeBound(weight)+CDPCThresholdsBits(thresholds)
  }
}

// Measure the stored rational pairs, including unreduced fields.
ghost function CDPCThresholdsBits(thresholds:CDPCThresholds<Rational>):nat
{
  RationalBits(thresholds.privateLower)+RationalBits(thresholds.privateUpper)+
  RationalBits(thresholds.fitnessLower)+RationalBits(thresholds.fitnessUpper)
}

ghost function CDPCInputSize<Q(!new)>(instance:CDPCInstance<Q>, interview:Interview<Q>, weight:Q -> nat):nat
{ instance.Size(weight)+interview.Size(weight) }

// Include the entire supplied interview in the verifier's input bound.
ghost function {:opaque} CDPCInputSizeBound<Q(!new)>(instance:CDPCInstance<Q>, interview:Interview<Q>, weight:Q -> nat):(size:nat)
  ensures instance.SizeBound(weight) <= size && interview.SizeBound(weight) <= size
  ensures instance.questions.SizeBound(weight) <= size
  ensures instance.fitness.SizeBound(weight, BoolBits, BoolBits) <= size
  ensures instance.multiplicity.SizeBound(weight, BoolBits, NatBits) <= size
  ensures instance.privateQuestions.SizeBound(weight) <= size
  ensures CDPCThresholdsBits(instance.thresholds) <= size
  ensures CDPCInputSize(instance, interview, weight) <= size
{ instance.SizeBound(weight)+interview.SizeBound(weight) }
