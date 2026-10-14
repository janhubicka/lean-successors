/-
# Successor v10 complete proof-build aggregation

All source modules of the frozen v10 validation are imported explicitly,
including intermediate lemmas that a final theorem might not transitively
use. Keep this module as a full compile target; do not turn it into a
minimal API that silently stops checking orphaned proof files. The public
entrypoints are in the concrete Kpt SMTree and Kpt Ramsey applications.

No theorem declarations or new axioms are introduced here.
-/

import SuccessorTree.V10.Counting
import SuccessorTree.V10.MeetTrace
import SuccessorTree.V10.BlockOrder
import SuccessorTree.V10.MeetBundle
import SuccessorTree.V10.FirstDisagreement
import SuccessorTree.V10.MeetProvenance
import SuccessorTree.V10.SocleBound
import SuccessorTree.V10.AncestorMeet
import SuccessorTree.V10.SocleE
import SuccessorTree.V10.RecordBridge
import SuccessorTree.V10.OriginalPool
import SuccessorTree.V10.HRelations
import SuccessorTree.V10.OriginalPoolEnvelope
import SuccessorTree.V10.CanonicalParameters
import SuccessorTree.V10.CanonicalObservation
import SuccessorTree.V10.HAge
import SuccessorTree.V10.HGenerationRank
import SuccessorTree.V10.HRelocation
import SuccessorTree.V10.RelocationCopy
import SuccessorTree.V10.RelocationIrreducible
import SuccessorTree.V10.RelocationOrder
import SuccessorTree.V10.FiniteMeetBudget
import SuccessorTree.V10.HAgeProjection
import SuccessorTree.V10.SignatureSplice
import SuccessorTree.V10.SignatureProfiles
import SuccessorTree.V10.SignatureTypePrefix
import SuccessorTree.V10.SignatureCollision
import SuccessorTree.V10.AmbientSignature
import SuccessorTree.V10.RelationalTypeReduct
import SuccessorTree.V10.EFreeLevel
import SuccessorTree.V10.PartialStructureE
import SuccessorTree.V10.HExactE
import SuccessorTree.V10.PartialTypeRestriction
import SuccessorTree.V10.HELinkage
import SuccessorTree.V10.CommonSocleType
import SuccessorTree.V10.FirstFullPrefix
import SuccessorTree.V10.RawTypeMeet
import SuccessorTree.V10.RawMeetLevel
import SuccessorTree.V10.RawPrefixOrder
import SuccessorTree.V10.PrefixReplicaE
import SuccessorTree.V10.PrefixReplicaL
import SuccessorTree.V10.PrefixReplicaPartial
import SuccessorTree.V10.PrefixReplicaAge
import SuccessorTree.V10.AdmissibleKptPrefix

import SuccessorTree.V10.FiniteKptLevels
import SuccessorTree.V10.RawPrefixMeet
import SuccessorTree.V10.RawPartialTypeLevelTree
import SuccessorTree.V10.AdmissibleKptMeet
import SuccessorTree.V10.AdmissibleKptLevelTree
import SuccessorTree.V10.CanonicalBinary
import SuccessorTree.V10.CanonicalInsertionParameter

import SuccessorTree.V10.CanonicalCrossing

import SuccessorTree.V10.CompleteNextColumn

import SuccessorTree.V10.ExtractSuccessorComponents

import SuccessorTree.V10.ParameterLetterUniqueness

import SuccessorTree.V10.ExtractedSuccessorS2

import SuccessorTree.V10.EmptyParameterS2

import SuccessorTree.V10.CanonicalStepGraph

import SuccessorTree.V10.CanonicalStepRealization

import SuccessorTree.V10.CanonicalCoverS3

import SuccessorTree.V10.CanonicalStepUniqueness

import SuccessorTree.V10.CanonicalRawSTree

import SuccessorTree.V10.TerminalLetterReplica

import SuccessorTree.V10.TerminalLetterAge

import SuccessorTree.V10.AdmissibleSigmaSTree

import SuccessorTree.V10.ConcreteKptM1

import SuccessorTree.V10.HNumericBinary

import SuccessorTree.V10.HDirectedTraces

import SuccessorTree.V10.HIncidentTrace

import SuccessorTree.V10.HFiniteAge

import SuccessorTree.V10.HClosureCharge

import SuccessorTree.V10.ActualCrossingSignature

import SuccessorTree.V10.LocalAgeNeutral

import SuccessorTree.V10.LocalAgeAllLevels

import SuccessorTree.V10.EndDuplicateAge

import SuccessorTree.V10.LevelRemovalFreeCut
import SuccessorTree.V10.LevelRemovalType
import SuccessorTree.V10.LevelRemovalUniformFunction
import SuccessorTree.V10.LevelRemovalUniformLevel
import SuccessorTree.V10.LevelRemovalUniformOrder
import SuccessorTree.V10.LevelRemovalUnifiedParameter
import SuccessorTree.V10.LevelRemovalHighStepSafety
import SuccessorTree.V10.LevelRemovalUniformParameter
import SuccessorTree.V10.LevelRemovalCanonicalStepAssembly
import SuccessorTree.V10.LevelRemovalDeletedWeakTarget
import SuccessorTree.V10.LevelRemovalUniformLowWeakSucc
import SuccessorTree.V10.LevelRemovalUniformHighWeakSucc
import SuccessorTree.V10.LevelRemovalUniformShapeMap
import SuccessorTree.V10.LevelRemovalM2Criterion
import SuccessorTree.V10.LevelRemovalSkipsOnly
import SuccessorTree.V10.LevelRemovalM2ExactExtension
import SuccessorTree.V10.LevelRemovalBoundaryRestoration
import SuccessorTree.V10.LevelRemovalFullRangeRestoration
import SuccessorTree.V10.LevelRemovalFullRangeOrder
import SuccessorTree.V10.LevelRemovalTopDeletePrefix
import SuccessorTree.V10.LocalAgeOneLinkedUpper
import SuccessorTree.V10.LevelRemovalColumnTransport
import SuccessorTree.V10.LevelRemovalTerminalLetter
import SuccessorTree.V10.LevelRemovalRawPrefix
import SuccessorTree.V10.LevelRemovalCrossGapPrefix
import SuccessorTree.V10.LevelRemovalBoundaryWeakSucc
import SuccessorTree.V10.LevelRemovalPrefixCommute
import SuccessorTree.V10.LevelRemovalParameter
import SuccessorTree.V10.LevelRemovalCanonicalParameter
import SuccessorTree.V10.LevelRemovalAdmissibleType
import SuccessorTree.V10.LevelRemovalAdmissiblePrefix
import SuccessorTree.V10.LevelRemovalWitnessCut
import SuccessorTree.V10.LevelRemovalPrefixCut
import SuccessorTree.V10.LevelRemovalGapColumn
import SuccessorTree.V10.LevelRemovalGapSeparation
import SuccessorTree.V10.LevelRemovalUniformImageGuard
import SuccessorTree.V10.LevelRemovalIntrinsicAdmissible
import SuccessorTree.V10.LevelRemovalBoundaryAdmissible
import SuccessorTree.V10.LevelRemovalAllLevelsAdmissible

import SuccessorTree.V10.PrescribedB3Spacing

import SuccessorTree.V10.PrescribedMatchingFinite

import SuccessorTree.V10.PrescribedCorrectedB3

-- Public endpoint of the checked prescribed one-gap boring extension.
import SuccessorTree.V10.PrescribedBoringCompletion

-- M3: concrete normalized earlier-successor duplication and witness independence.
import SuccessorTree.V10.M3RepresentativeIndependence
import SuccessorTree.V10.M3CombinedEndpoint
import SuccessorTree.V10.M3LiteralDuplication
import SuccessorTree.V10.LevelRemovalSourceSuccessor

-- M2-independent full retained-record recovery and standard-axiom audit.
import SuccessorTree.V10.M2RecoveryAxiomAudit

-- M2-independent canonical-parameter prefix transport.
import SuccessorTree.V10.M2ParameterPrefixAxiomAudit

-- Single finite padded source witness, closed to a genuine Kpt type.
import SuccessorTree.V10.M2SocleCapAxiomAudit

-- M2: finite induced L-age transfer for the non-edge witness.
import SuccessorTree.V10.M2InducedAgeTransfer

import SuccessorTree.V10.CanonicalPrefixStep
import SuccessorTree.V10.ContainedCanonicalParameter
import SuccessorTree.V10.ShapeMapAmbientOrdinaryTransport
import SuccessorTree.V10.M2CapTypesAxiomAudit

-- M2: factorization from actual compatible boundary data, with no global extension premise.
import SuccessorTree.V10.M2CompatibleFactorization

import SuccessorTree.V10.M2BadCopySourceAge
import SuccessorTree.V10.M2BoundedCopySourceAge
import SuccessorTree.V10.M2NeutralCarrierFill
import SuccessorTree.V10.M2SparsePullbackAge
import SuccessorTree.V10.PrescribedB3BoundedCores
import SuccessorTree.V10.M2SourceTypeAge
import SuccessorTree.V10.M2NonedgePairAge

import SuccessorTree.V10.M2JointImageCompatibility

-- M2: compatibility of complete image socles from a joint nonedge source witness.
import SuccessorTree.V10.M2TwoTypeImageCompatibility

-- M2 B2: full ordinary L+ compatibility reflection and transfer across shape maps.
import SuccessorTree.V10.M2B2Transfer

-- M2 finite B3: real selected vertices retain full directed L records.
import SuccessorTree.V10.M2BoundedCopyRecords

-- M2: B1/B2 family packaging at the deletion boundary.
import SuccessorTree.V10.M2BoundaryFamily

-- M2 B3: selected compatible types admit one padded source witness.
import SuccessorTree.V10.M2SelectedFamilyPadding

-- M2 B3: ordered final copy coordinates and exact atomwise transfer.
import SuccessorTree.V10.M2CopyImageCoordinates
import SuccessorTree.V10.M2CopyImageTransfer

-- M2: selected finite-copy L-types recovered from the actual shape map.
import SuccessorTree.V10.M2SelectedCopyType
import SuccessorTree.V10.M2SelectedCopyPadded

-- M2: complete ordinary image types in a single capped padded witness.
import SuccessorTree.V10.M2AmbientLevelTransport
import SuccessorTree.V10.M2SelectedCapTransport
import SuccessorTree.V10.M2ImageOrdinaryZone

-- M2: complete ordinary pair and singleton retention inside one capped image.
import SuccessorTree.V10.M2CapRetainedAtoms

-- M2: exact padded L-model, upper-pair and full lower-socle image record.
import SuccessorTree.V10.M2CapPaddedRecords
import SuccessorTree.V10.M2ImageLowerSocle

-- M2 B3: exact induced copy from lower/upper pair and singleton zones.
import SuccessorTree.V10.M2CopyFromCompleteImageTypes

-- M2 B3: concrete padded witness and recovery of the initial socle.
import SuccessorTree.V10.M2ConcreteCapImageCopy
import SuccessorTree.V10.M2InitialSocleFromUpper

-- M2 B3: separate the zero-upper case and recover the cap socle from an upper record.
import SuccessorTree.V10.M2B3CopyCases

-- M2 B3: full selected source witness yields forbidden-copy contradiction.
import SuccessorTree.V10.M2B3SelectedContradiction

-- M2 B3: prescribed ordinary socle is forbidden-free by induced age.
import SuccessorTree.V10.M2B3SocleAge

-- M2: real typed boundary D(x) and F(x), source injectivity, full B1.
import SuccessorTree.V10.M2BoundaryTypedRecords

-- M2: actual B1/B2 prescribed data covering the entire deleted boundary.
import SuccessorTree.V10.M2BoundaryPrescribedB2

-- M2: actual boundary B1/B2/targets/coverage; factorization needs only B3.
import SuccessorTree.V10.M2BoundaryFinalCriterion

-- M2 B3: every compatible upper finite-age type has a genuine F-source label.
import SuccessorTree.V10.M2BoundaryUpperSelection

-- M2 B3: all source ordinary L atoms recovered at retained image levels.
import SuccessorTree.V10.M2BoundaryLowRecords

-- M2 B3: compatibility of actual original source types reflected from D.
import SuccessorTree.V10.M2BoundaryOriginalCompatibility

-- M2: unconditional compatible finite L-age B3 and first-gap factorization.
import SuccessorTree.V10.M2BoundaryCompatibleB3Closure

-- M2: exact normalized monoid axiom from actual finite-age factorization.
import SuccessorTree.V10.M2FullAxiom

-- Full normalized Kpt successor tree with M1, M2 and literal M3.
import SuccessorTree.V10.KptCompleteSMTree

-- Concrete Ramsey consequences of the now-verified normalized Kpt SMTree.
import SuccessorTree.V10.KptRamseyApplications

-- Section 6: finite I3 failure witnesses and selected original-name signatures.
import SuccessorTree.V10.I3AgeFailure
import SuccessorTree.V10.ChosenAgeSignatures

-- I3: actual prescribed-source upper types recover ambient original labels.
import SuccessorTree.V10.I3PrescribedOriginalWitness

-- Section 6.44: the manuscript's descending cardinal recurrence.
import SuccessorTree.V10.EnvelopeNumericalRecurrence

-- I3: exact original-valued signatures and cardinal bound R(M).
import SuccessorTree.V10.I3SignatureCardinality
import SuccessorTree.V10.I3AmbientPrescribedPool
import SuccessorTree.V10.I3AmbientSocleBridge

-- I3: recover numeric H generators and upper original gates from actual age copies.
import SuccessorTree.V10.I3CrossingAtoms

-- I3 Lemma 6.53: complete as-written numerical H relation relocation.
import SuccessorTree.V10.I3NumericRelocation
import SuccessorTree.V10.I3WitnessCrossRelocation
import SuccessorTree.V10.I3WitnessLowerRelocation
import SuccessorTree.V10.I3FullForbiddenRelocation

-- I3: unique nonempty proper lower prefix at the tested coordinate.
import SuccessorTree.V10.I3ForbiddenCutIndex

-- I3: forbidden-free ambient socle forces the copy's nonempty proper lower cut.
import SuccessorTree.V10.I3ActualProperCut

-- Lemma 6.53: all actual witness rank/generation conclusions, no coordinate hypotheses.
import SuccessorTree.V10.I3ActualWitnessGeneration

-- Lemma 6.53: actual H ambient pool failed B3 forces proper-cut and generation bounds.
import SuccessorTree.V10.I3ActualStageGeneration

-- I3: level-filtered originals of the fixed pool (complete B1/B2 and admissibility).
import SuccessorTree.V10.I3EligibleStagePool

-- I3: finite failed B3 on cut-filtered pool, actual generation and labels.
import SuccessorTree.V10.I3EligibleStageWitness

-- Observation 6.52: derive finite R(M) bound for actual failed I3 stage tests.
import SuccessorTree.V10.I3StageSignatureBound

-- I3: selected closure pool and exact f_ell source/graph identification criterion.
import SuccessorTree.V10.I3SelectedStagePool

-- Lemma 6.53: chosen signature original labels themselves have higher generation.
import SuccessorTree.V10.I3ChosenOriginalGeneration

-- Observation 6.52: variable selected sources, real f_ell failures and R(M).
import SuccessorTree.V10.I3SelectedStageSignature

-- I3: reconstruct variable selected stage names from the actual prescribed graph.
import SuccessorTree.V10.I3ActualGraphRepresentation

-- I3: derive actual source-to-original graph from represented closure prefixes.
import SuccessorTree.V10.I3ClosureCrossingGraph

-- I3: non-skippable complete closure crossing contradicts one-gap B3 extension.
import SuccessorTree.V10.I3NoSkipForcesB3

-- I3: construct selected closure crossing and derive corrected B3 failure and R(M).
import SuccessorTree.V10.I3ClosureSelectedCrossing

-- Algorithm 5.4: actual I3 interesting levels force corrected B3 failure.
import SuccessorTree.V10.I3AlgorithmInterestingBridge

-- Proposition 6.44: sharp I3 signatures from names of higher-generation originals.
import SuccessorTree.V10.I3HigherSignatureCapacity

-- I3: numerical H failed-B3 witnesses have only higher-generation original names.
import SuccessorTree.V10.I3ActualHigherSignature
