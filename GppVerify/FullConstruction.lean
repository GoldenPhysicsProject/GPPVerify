import GppVerify

-- Hadamard / Shadow-Euler finite algebra
import GppVerify.NumberTheory.HadamardShadowPairAlgebra
import GppVerify.NumberTheory.ShadowEulerFiniteCore

-- Principal-series / Riemann-celestial affine structure
import GppVerify.RiemannHypothesis.CelestialRiemannAffineBridge
import GppVerify.CelestialHolography.PositiveRealPrincipalSeries
import GppVerify.CelestialHolography.CompletedZetaPrincipalSeriesResponse
import GppVerify.CelestialHolography.CompletedZetaDilationUnitaryBridge

-- Global completion / logarithmic-derivative separation
import GppVerify.RiemannHypothesis.GlobalCompletedFactorization
import GppVerify.RiemannHypothesis.LogDerivativeProduct

-- Exact PGL(2,R)-representative orientation sign channel for the 1D conformal thread
import GppVerify.RiemannHypothesis.PGL2OrientationAlgebra

-- Grassmannian / googly / orientation / zitterbewegung structure
import GppVerify.GrassmannianOrientationZ4
import GppVerify.CelestialHolography.GooglyAntiunitaryExchange
import GppVerify.CelestialHolography.GooglyTwistorLift
import GppVerify.StandardModel.MassOrientationCoupling

-- Prime Poisson / positive-type / causal heat arithmetic
import GppVerify.RiemannHypothesis.VonMangoldtPrimePowerPoissonFiber
import GppVerify.RiemannHypothesis.PrimePoissonRadialPositiveType
import GppVerify.RiemannHypothesis.FinitePrimePoissonRadialSum
import GppVerify.RiemannHypothesis.PositiveTypeLimit
import GppVerify.RiemannHypothesis.CosinePositiveType
import GppVerify.RiemannHypothesis.CausalHeatPrimePowerAnomaly
import GppVerify.RiemannHypothesis.CausalHeatVonMangoldtReindex
import GppVerify.RiemannHypothesis.FiniteHeatSemigroupGram
import GppVerify.RiemannHypothesis.FiniteHeatSemigroupMonotonicity
import GppVerify.RiemannHypothesis.LocalEulerShadowColligation

-- Prime-response transfer / arithmetic defect
import GppVerify.RiemannHypothesis.PrimeResponseContraction
import GppVerify.RiemannHypothesis.PrimeResponseTransferOperator

-- Strict normalized prime-Fisher and zeta-Gibbs fluctuation geometry / thermodynamics
import GppVerify.RiemannHypothesis.PrimeFisherCenteredGeometry
import GppVerify.RiemannHypothesis.PrimeFisherCenteredDeterminant
import GppVerify.RiemannHypothesis.TwoParameterFisherDeterminant
import GppVerify.RiemannHypothesis.PrimeFisherTwoParameterStrict
import GppVerify.RiemannHypothesis.PrimeHankelAllOrderStrict
import GppVerify.RiemannHypothesis.ZetaGibbsCenteredMomentBridge
import GppVerify.RiemannHypothesis.ZetaGibbsStrictThermodynamics

-- Exact sech / Wiener-Hopf / Gamma / Mehler-Fock spectral structure
import GppVerify.RiemannHypothesis.SechSixthIntegral
import GppVerify.CelestialHolography.WienerHopfGammaChamberPositiveFactor
import GppVerify.CelestialHolography.WienerHopfGammaChamberHierarchy
import GppVerify.CelestialHolography.MehlerFockGammaCollapsedWeight
import GppVerify.QuantumGravity.SpectralRhoChamberProduct
import GppVerify.QuantumGravity.SpectralRhoMehlerFockBridge

-- Scalar-box regulator, simplex majorant closure, and physical convergence
import GppVerify.CelestialHolography.RaisedBoxSimplexGammaClosure
import GppVerify.CelestialHolography.RaisedBoxConcreteVolumeClosure
import GppVerify.CelestialHolography.RaisedBoxRealMajorantIntegrability
import GppVerify.CelestialHolography.RaisedBoxRealMajorantSlice
import GppVerify.CelestialHolography.RaisedBoxRealMajorantSliceIntegral
import GppVerify.CelestialHolography.RaisedBoxRealMajorantMiddleIntegral
import GppVerify.CelestialHolography.RaisedBoxRealOuterDomination
import GppVerify.CelestialHolography.ScalarBoxRegulatorAlgebra
import GppVerify.CelestialHolography.PositiveRegulatorEventuallySmall
import GppVerify.CelestialHolography.ScalarBoxAutomaticRegulatorConvergence

-- D-dimensional / massive celestial cut closure
import GppVerify.CelestialHolography.MassiveVectorPhysicalChartClosure
import GppVerify.CelestialHolography.MassiveCutRadialMu4Weight
import GppVerify.CelestialHolography.MassiveCutMu4RadialMoment
import GppVerify.CelestialHolography.TwoFlowScalarStateSum

-- Quantum-information / Standard-Model finite cores
import GppVerify.StandardModel.UniversalNotFidelity

/-!
# GPPVerify full construction umbrella

`GppVerify.lean` is the historical root module. During rapid research, a number of
proved modules were added behind focused CI lanes without immediately becoming imports
of that root. This umbrella makes the current integration frontier import-connected.

The repository's ordinary `lake build` remains the stronger file-level compilation gate:
it builds the full `GppVerify` Lean library. Building this module additionally checks
that the active proved construction can coexist in one import graph. No marker theorem
is needed: successful elaboration of the imports is the gate.
-/
