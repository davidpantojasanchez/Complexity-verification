include "CDPC.dfy"
include "../Foundations/CollectionSizes.dfy"
include "../Arithmetic/CostedArithmetic.dfy"

// Stored rational pairs include unreduced fields. The real-threshold
// mathematical instance remains separate.
type CDPCRationalInstance<Q(==)> = (set<Q>, map<Candidate<Q>, bool>,
  map<Candidate<Q>, nat>, set<Q>, Rational, Rational, Rational, Rational)

ghost function CDPCThresholdsBits(thresholds:(Rational, Rational, Rational, Rational)):nat
{ RationalBits(thresholds.0)+RationalBits(thresholds.1)+RationalBits(thresholds.2)+RationalBits(thresholds.3) }

ghost function CDPCInstanceSize<Q(!new)>(questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    thresholds:(Rational, Rational, Rational, Rational), weight:Q -> nat):nat
{
  5+Size_set(questions, weight)+Size_set(privateQuestions, weight)+
  Size_map(fitness, (candidate:Candidate<Q>) => Size_map_t_bool(candidate, weight), BoolBits)+
  Size_map(multiplicity, (candidate:Candidate<Q>) => Size_map_t_bool(candidate, weight), NatBits)+
  CDPCThresholdsBits(thresholds)
}

ghost function CDPCCertificateSize<Q>(certificate:InterviewModel<Q>, weight:Q -> nat):nat
{ InterviewSize(certificate, weight) }

ghost function CDPCInputSize<Q(!new)>(questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    thresholds:(Rational, Rational, Rational, Rational), interview:InterviewModel<Q>, weight:Q -> nat):nat
{ CDPCInstanceSize(questions, fitness, multiplicity, privateQuestions, thresholds, weight)+CDPCCertificateSize(interview, weight) }
