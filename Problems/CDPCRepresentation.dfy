include "CDPC.dfy"
include "../Foundations/ExactCollectionSizes.dfy"
include "../Foundations/RepresentationBounds.dfy"
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
}

// The compound-label representation still needs its pending label adapter.
datatype CDPCSetInstance<T(==)> = CDPCSetInstance(questions:SetSet<T>, fitness:Map_MapSet_T<T, bool, bool>,
  multiplicity:Map_MapSet_T<T, bool, nat>, privateQuestions:SetSet<T>, thresholds:CDPCThresholds<Rational>)

// Measure the stored rational pairs, including unreduced fields.
ghost function CDPCThresholdsBits(thresholds:CDPCThresholds<Rational>):nat
{
  RationalBits(thresholds.privateLower)+RationalBits(thresholds.privateUpper)+
  RationalBits(thresholds.fitnessLower)+RationalBits(thresholds.fitnessUpper)
}

ghost function CDPCInstanceSize<Q(!new)>(questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    thresholds:CDPCThresholds<Rational>, weight:Q -> nat):nat
{
  5+Size_set(questions, weight)+Size_set(privateQuestions, weight)+
  Size_map(fitness, (candidate:Candidate<Q>) => Size_map(candidate, weight, BoolBits), BoolBits)+
  Size_map(multiplicity, (candidate:Candidate<Q>) => Size_map(candidate, weight, BoolBits), NatBits)+
  CDPCThresholdsBits(thresholds)
}

ghost function CDPCCertificateSize<Q>(certificate:InterviewModel<Q>, weight:Q -> nat):nat
{ InterviewSize(certificate, weight) }

ghost function CDPCInputSize<Q(!new)>(questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    thresholds:CDPCThresholds<Rational>, interview:InterviewModel<Q>, weight:Q -> nat):nat
{ CDPCInstanceSize(questions, fitness, multiplicity, privateQuestions, thresholds, weight)+CDPCCertificateSize(interview, weight) }

// Bound the models of the supplied instance and interview using the canonical
// headers and stored fields. Retained collection universes are separate.
ghost function {:opaque} CDPCInputSizeBound<Q(!new)>(instance:CDPCInstance<Q>, interview:Interview<Q>, weight:Q -> nat):(size:nat)
  ensures instance.questions.SizeBound(weight) <= size
  ensures instance.fitness.SizeBound(weight, BoolBits, BoolBits) <= size
  ensures instance.multiplicity.SizeBound(weight, BoolBits, NatBits) <= size
  ensures instance.privateQuestions.SizeBound(weight) <= size
  ensures CDPCThresholdsBits(instance.thresholds) <= size && interview.SizeBound(weight) <= size
  ensures CDPCInputSize(instance.questions.Model(), instance.fitness.Model(), instance.multiplicity.Model(),
    instance.privateQuestions.Model(), instance.thresholds, interview.Model(), weight) <= size
{
  var questions, fitness, multiplicity, privateQuestions, thresholds :=
    instance.questions, instance.fitness, instance.multiplicity, instance.privateQuestions, instance.thresholds;
  representation_bound_set(questions.Model(), weight);
  representation_bound_map_map_t(fitness.Model(), weight, BoolBits, BoolBits);
  representation_bound_map_map_t(multiplicity.Model(), weight, BoolBits, NatBits);
  representation_bound_set(privateQuestions.Model(), weight);
  interview_representation_bound(interview.Model(), weight);
  5+questions.SizeBound(weight)+fitness.SizeBound(weight, BoolBits, BoolBits)+
    multiplicity.SizeBound(weight, BoolBits, NatBits)+privateQuestions.SizeBound(weight)+
    CDPCThresholdsBits(thresholds)+interview.SizeBound(weight)
}
