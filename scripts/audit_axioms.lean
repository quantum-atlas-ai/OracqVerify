import OracqVerify.Generators.Registry
import OracqVerify.RIR.ScopedLinkError
import OracqVerify.RIR.SelectPrepareWord
import OracqVerify.Verification.ApproximatePhase
import OracqVerify.Verification.LCHSCertificate
import OracqVerify.Verification.LCHSFullArithmetic
import OracqVerify.Verification.WideGroverBinding
import OracqVerify.Verification.WideLCHS

#print axioms OracqVerify.RIR.verifyScopedSourceLink_iff
#print axioms OracqVerify.RIR.ScopedSourceLink.sound
#print axioms OracqVerify.RIR.ScopedSourceLink.distance_le
#print axioms OracqVerify.RIR.weighted_blocks_error
#print axioms OracqVerify.RIR.selectPrepare_compress
#print axioms OracqVerify.RIR.SelectLayout.word_matrix
#print axioms OracqVerify.Verification.ApproximatePhase.Certificate.sound
#print axioms OracqVerify.Generators.DeutschJozsa.generate_correct
#print axioms OracqVerify.Verification.DeutschJozsa.BoundCertificate.correct
#print axioms OracqVerify.Generators.Grover.generate_correct
#print axioms OracqVerify.Verification.Grover.Certificate.probability
#print axioms OracqVerify.Verification.WideGrover.Certificate.sound
#print axioms OracqVerify.Verification.LCHS.LinkedAssembly.sound
#print axioms OracqVerify.Verification.WideLCHS.Certificate.sound
#print axioms OracqVerify.Verification.LCHS.firstBranch_polynomial_error
#print axioms OracqVerify.Verification.LCHS.checked_columns
