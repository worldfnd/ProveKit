package main

import (
	"fmt"
	"log"
	"os"

	"reilabs/whir-verifier-circuit/typeConverters"
	"reilabs/whir-verifier-circuit/utilities"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"github.com/consensys/gnark/std/math/uints"
)

type Circuit struct {
	// Inputs
	LinearStatementValuesAtPoints []frontend.Variable
	LinearStatementEvaluations    []frontend.Variable
	LogNumConstraints             int
	LogNumVariables               int
	LogANumTerms                  int
	SpartanMerkle                 Merkle
	SparkValueMerkle              Merkle
	WHIRParamsCol                 WHIRParams
	WHIRParamsRow                 WHIRParams
	WHIRParamsA                   WHIRParams
	// Public Input
	IO         []byte
	Transcript []uints.U8 `gnark:",public"`
}

func (circuit *Circuit) Define(api frontend.API) error {
	sc, arthur, uapi, err := initializeComponents(api, circuit)
	if err != nil {
		return err
	}

	tRand := make([]frontend.Variable, circuit.LogNumConstraints)
	err = arthur.FillChallengeScalars(tRand)
	if err != nil {
		return err
	}

	spartanSumcheckRand, spartanSumcheckLastValue, err := runSumcheck(api, arthur, frontend.Variable(0), circuit.LogNumConstraints, 4)
	if err != nil {
		return err
	}

	err = runWhir(api, arthur, uapi, sc, circuit.SpartanMerkle, circuit.WHIRParamsCol, circuit.LinearStatementEvaluations, circuit.LinearStatementValuesAtPoints)
	if err != nil {
		return err
	}

	x := api.Mul(api.Sub(api.Mul(circuit.LinearStatementEvaluations[0], circuit.LinearStatementEvaluations[1]), circuit.LinearStatementEvaluations[2]), calculateEQ(api, spartanSumcheckRand, tRand))
	api.AssertIsEqual(spartanSumcheckLastValue, x)

	rowRootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(rowRootHash); err != nil {
		return err
	}

	_, _, err = FillInOODPointsAndAnswers(circuit.WHIRParamsA.CommittmentOODSamples, arthur)
	if err != nil {
		return err
	}

	colRootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(colRootHash); err != nil {
		return err
	}

	_, _, err = FillInOODPointsAndAnswers(circuit.WHIRParamsA.CommittmentOODSamples, arthur)
	if err != nil {
		return err
	}

	valRootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(valRootHash); err != nil {
		return err
	}

	_, _, err = FillInOODPointsAndAnswers(circuit.WHIRParamsA.CommittmentOODSamples, arthur)
	if err != nil {
		return err
	}

	eRxRootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(eRxRootHash); err != nil {
		return err
	}

	_, _, err = FillInOODPointsAndAnswers(circuit.WHIRParamsA.CommittmentOODSamples, arthur)
	if err != nil {
		return err
	}
	eRyRootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(eRyRootHash); err != nil {
		return err
	}

	_, _, err = FillInOODPointsAndAnswers(circuit.WHIRParamsA.CommittmentOODSamples, arthur)
	if err != nil {
		return err
	}
	readTSRowRootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(readTSRowRootHash); err != nil {
		return err
	}

	_, _, err = FillInOODPointsAndAnswers(circuit.WHIRParamsA.CommittmentOODSamples, arthur)
	if err != nil {
		return err
	}
	readTSColRootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(readTSColRootHash); err != nil {
		return err
	}

	_, _, err = FillInOODPointsAndAnswers(circuit.WHIRParamsA.CommittmentOODSamples, arthur)
	if err != nil {
		return err
	}
	finalCTSRowRootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(finalCTSRowRootHash); err != nil {
		return err
	}

	_, _, err = FillInOODPointsAndAnswers(circuit.WHIRParamsCol.CommittmentOODSamples, arthur)
	if err != nil {
		return err
	}
	finalCTSColRootHash := make([]frontend.Variable, 1)
	if err := arthur.FillNextScalars(finalCTSColRootHash); err != nil {
		return err
	}

	_, _, err = FillInOODPointsAndAnswers(circuit.WHIRParamsRow.CommittmentOODSamples, arthur)
	if err != nil {
		return err
	}

	_, _, err = runSumcheck(api, arthur, circuit.LinearStatementValuesAtPoints[0], circuit.LogANumTerms, 4)
	if err != nil {
		return err
	}
	return nil
}

func verifyCircuit(
	deferred []Fp256, cfg Config, hints Hints, pk *groth16.ProvingKey, vk *groth16.VerifyingKey, outputCcsPath string, claimedEvaluations []Fp256,
) {
	transcriptT := make([]uints.U8, cfg.TranscriptLen)
	contTranscript := make([]uints.U8, cfg.TranscriptLen)

	for i := range cfg.Transcript {
		transcriptT[i] = uints.NewU8(cfg.Transcript[i])
	}

	linearStatementValuesAtPoints := make([]frontend.Variable, len(deferred))
	contLinearStatementValuesAtPoints := make([]frontend.Variable, len(deferred))

	linearStatementEvaluations := make([]frontend.Variable, len(claimedEvaluations))
	contLinearStatementEvaluations := make([]frontend.Variable, len(claimedEvaluations))
	for i := range len(deferred) {
		linearStatementValuesAtPoints[i] = typeConverters.LimbsToBigIntMod(deferred[i].Limbs)
		linearStatementEvaluations[i] = typeConverters.LimbsToBigIntMod(claimedEvaluations[i].Limbs)
	}

	var circuit = Circuit{
		IO:                []byte(cfg.IOPattern),
		Transcript:        contTranscript,
		LogNumConstraints: cfg.LogNumConstraints,
		LogNumVariables:   cfg.LogNumVariables,
		LogANumTerms:      cfg.LogANumTerms,

		LinearStatementEvaluations:    contLinearStatementEvaluations,
		LinearStatementValuesAtPoints: contLinearStatementValuesAtPoints,
		SpartanMerkle:                 newMerkle(hints.colHints, true),
		SparkValueMerkle:              newMerkle(hints.aHints, true),

		WHIRParamsCol: new_whir_params(cfg.WHIRConfigCol), WHIRParamsRow: new_whir_params(cfg.WHIRConfigRow),
		WHIRParamsA: new_whir_params(cfg.WHIRConfigA),
	}

	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, &circuit)
	if err != nil {
		log.Fatalf("Failed to compile circuit: %v", err)
	}
	if outputCcsPath != "" {
		ccsFile, err := os.Create(outputCcsPath)
		if err != nil {
			log.Printf("Cannot create ccs file %s: %v", outputCcsPath, err)
		} else {
			_, err = ccs.WriteTo(ccsFile)
			if err != nil {
				log.Printf("Cannot write ccs file %s: %v", outputCcsPath, err)
			}
		}
		log.Printf("ccs written to %s", outputCcsPath)
	}

	if pk == nil || vk == nil {
		log.Printf("PK/VK not provided, generating new keys unsafely. Consider providing keys from an MPC ceremony.")
		unsafePk, unsafeVk, err := groth16.Setup(ccs)
		if err != nil {
			log.Fatalf("Failed to setup groth16: %v", err)
		}
		pk = &unsafePk
		vk = &unsafeVk
	}

	assignment := Circuit{
		IO:                []byte(cfg.IOPattern),
		Transcript:        transcriptT,
		LogNumConstraints: cfg.LogNumConstraints,

		LinearStatementEvaluations:    linearStatementEvaluations,
		LinearStatementValuesAtPoints: linearStatementValuesAtPoints,
		SpartanMerkle:                 newMerkle(hints.colHints, false),
		SparkValueMerkle:              newMerkle(hints.aHints, false),

		WHIRParamsCol: new_whir_params(cfg.WHIRConfigCol),
		WHIRParamsRow: new_whir_params(cfg.WHIRConfigRow),
		WHIRParamsA:   new_whir_params(cfg.WHIRConfigA),
	}

	witness, _ := frontend.NewWitness(&assignment, ecc.BN254.ScalarField())
	publicWitness, _ := witness.Public()
	proof, _ := groth16.Prove(ccs, *pk, witness, backend.WithSolverOptions(solver.WithHints(utilities.IndexOf)))
	err = groth16.Verify(proof, *vk, publicWitness)
	if err != nil {
		fmt.Println(err)
	}
}
