package smtcomp;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class PostProcessUnsatCoreTrack {
	private static final String INPUT_FILE_NAME = "/home/matthias/ultimate/Concatenation_Job21979_and_Job22062.csv";
	private static final String OUTPUT_FILE_NAME = "/home/matthias/ultimate/Concatenation_Job21979_and_Job22062_RevisedResults.csv";
	private static final String NO_CONSENSUS_OUTPUT_FILE_NAME = "/home/matthias/ultimate/Concatenation_Job21979_and_Job22062_NoValidationConsensus.csv";

	// @formatter:off
	private static final String SOLVER_CVC4 = "CVC4-smtcomp2017-unsat-cores-fixed";
	private static final String SOLVER_MATHSAT = "mathsat-5.4.1-linux-x86_64-Unsat-Core";
	private static final String SOLVER_SMTINTERPOL = "SMTInterpol";
	private static final String SOLVER_Z3 = "z3-4.5.0";
	
	
	private static final String VALIDATION_CVC4 = "validation-check-sat-result_cvc4";
	private static final String VALIDATION_MATHSAT = "validation-check-sat-result_mathsat";
	private static final String VALIDATION_VAMPIRE = "validation-check-sat-result_vampire";
	private static final String VALIDATION_Z3 = "validation-check-sat-result_z3";
	private static final String[] VALIDATION_ORIGINAL = new String[] { 
			VALIDATION_CVC4, VALIDATION_MATHSAT, VALIDATION_VAMPIRE, VALIDATION_Z3 };

	private static final String VALIDATION_REVISED_CVC4 = "REVISED_validation-check-sat-result_cvc4";
	private static final String VALIDATION_REVISED_MATHSAT = "REVISED_validation-check-sat-result_mathsat";
	private static final String VALIDATION_REVISED_VAMPIRE = "REVISED_validation-check-sat-result_vampire";
	private static final String VALIDATION_REVISED_Z3 = "REVISED_validation-check-sat-result_z3";
	
	private static final String[] VALIDATION_REVISED = new String[] { 
			VALIDATION_REVISED_CVC4, VALIDATION_REVISED_MATHSAT, VALIDATION_REVISED_VAMPIRE, VALIDATION_REVISED_Z3 };
	

	private static final String CHECK_SAT_RESULT = "result";
	private static final String CHECK_SAT_RESULT_VALUE_UNKNOWN = "starexec-unknown";
	private static final String CHECK_SAT_IS_ERRONEOUS = "check-sat-result-is-erroneous"; // 0 or 1
	private static final String UC_PARSABLE = "parsable-unsat-core"; // true or false

	private static final String UC_SIZE = "size-unsat-core";
	private static final String ASSERTS_SIZE = "number-of-assert-commands";
	
	private static final String UC_VALIDATED = "unsat-core-validated"; // true or false
	private static final String REDUCTION = "reduction";
	private static final String RESULT_ERRONEOUS = "result-is-erroneous"; // 0 or 1
	private static final String REVISED_UC_VALIDATED = "REVISED_unsat-core-validated"; // true or false
	private static final String REVISED_REDUCTION = "REVISED_reduction";
	private static final String REVISED_RESULT_ERRONEOUS = "REVISED_result-is-erroneous"; // 0 or 1

	private static final Map<String, Integer> STATISTICS = new LinkedHashMap<>();
	private static final String STATISTICS_JOB_PAIRS = "job pairs";
	private static final String STATISTICS_CHECK_SAT_CORRECT  = "correct check-sat responses";
	private static final String STATISTICS_CHECK_SAT_INCORRECT  = "incorrect check-sat responses";
	private static final String STATISTICS_PARSABLE_UC  = "get-unsat-core responses";
	
	private static final String STATISTICS_VALIDATED_UC  = "times the unsatisfiable core was validated";
	private static final String STATISTICS_INVALID_UC  = "times the unsatisfiable core was not correct";
	private static final String STATISTICS_SELFINVALIDATED  = "times the unsatisfiable core was invalidated by the same solver";
	private static final String STATISTICS_DISAGREEMENT  = "times there was no consensus among the validating solvers";
	private static final String STATISTICS_NOTAPPROVED  = "times no independent validating solver approved the correctness of the unsatisfiable core";
	private static final List<Map<String, String>> LINES_WITHOUT_VALIDATION_CONSENSUS = new ArrayList<>();
	private static final Set<String> DIVISIONS_WITHOUT_FULL_UC_APPROVAL = new LinkedHashSet<>();
	
	private static final Map<String, String> SOLVER_VALIDATOR_MAP = new HashMap<>();
	
	private static void increment(final String statistics) {
		final int oldValue = STATISTICS.get(statistics);
		STATISTICS.put(statistics, oldValue + 1);
	}

	private static void initializeStatistics() {
		STATISTICS.put(STATISTICS_JOB_PAIRS, 0);
		STATISTICS.put(STATISTICS_CHECK_SAT_CORRECT, 0);
		STATISTICS.put(STATISTICS_CHECK_SAT_INCORRECT, 0);
		STATISTICS.put(STATISTICS_PARSABLE_UC, 0);
		STATISTICS.put(STATISTICS_VALIDATED_UC, 0);
		STATISTICS.put(STATISTICS_INVALID_UC, 0);
		STATISTICS.put(STATISTICS_SELFINVALIDATED, 0);
		STATISTICS.put(STATISTICS_DISAGREEMENT, 0);
		STATISTICS.put(STATISTICS_NOTAPPROVED, 0);
	}
	
	
	private static String printStatistics() {
		final StringBuilder sb = new StringBuilder();
		sb.append(printStatisticsLine(STATISTICS_JOB_PAIRS));
		sb.append(printStatisticsLine(STATISTICS_CHECK_SAT_CORRECT));
		sb.append(printStatisticsLine(STATISTICS_CHECK_SAT_INCORRECT));
		sb.append(printStatisticsLine(STATISTICS_PARSABLE_UC));
		sb.append(printStatisticsLine(STATISTICS_VALIDATED_UC));
		sb.append(printStatisticsLine(STATISTICS_INVALID_UC));
		sb.append(printStatisticsLine(STATISTICS_SELFINVALIDATED));
		sb.append(printStatisticsLine(STATISTICS_DISAGREEMENT));
		sb.append(printStatisticsLine(STATISTICS_NOTAPPROVED));
		return sb.toString();
	}
	
	private static String printStatisticsLine(final String statistics) {
		return String.format("%7d", STATISTICS.get(statistics)) + " " + statistics + System.lineSeparator();
	}
	
	
	

	private static final String[] DIVISIONS_ARRAY = new String[]{ 
			"ABVFP",
			"ALIA", "ANIA", 
			"AUFBVDTLIA", "AUFDTLIA",
			"AUFLIA", "AUFLIRA", "AUFNIRA", 
			"BV", "BVFP", "FP", "LIA", "LRA", "NIA", "NRA", 
			"QF_ABV", "QF_ABVFP", "QF_ALIA", "QF_ANIA", "QF_AUFBV", "QF_AUFLIA", "QF_AUFNIA", "QF_AX", 
			"QF_BV", "QF_BVFP",	
			"QF_DT", 
			"QF_FP", 
			"QF_IDL", "QF_LIA", "QF_LIRA", "QF_LRA", "QF_NIA", "QF_NIRA", "QF_NRA", "QF_RDL", "QF_UF", 
			"QF_UFBV", 
			"QF_UFIDL", "QF_UFLIA", "QF_UFLRA", "QF_UFNIA", "QF_UFNRA", "UF", 
			"UFBV", "UFDT", "UFDTLIA", "UFIDL", "UFLIA", "UFLRA", "UFNIA",
	};
	
	private static Set<String> DIVISIONS = new HashSet<>(Arrays.asList(DIVISIONS_ARRAY));
	
	private static final String[] DIVISIONS_CVC4 = new String[]{ 
			"ALIA",
			"AUFBVDTLIA", "AUFDTLIA",
			"AUFLIA", "AUFLIRA", "AUFNIRA", 
			"FP", "LIA", "LRA", "NIA", "NRA", 
			"QF_ABV", 
			"QF_ALIA", "QF_ANIA", "QF_AUFBV", "QF_AUFLIA", "QF_AUFNIA", "QF_AX", 
			"QF_BV",
			"QF_DT", 
			"QF_IDL", "QF_LIA", "QF_LIRA", "QF_LRA", "QF_NIA", "QF_NIRA", "QF_NRA", "QF_RDL", "QF_UF", 
			"QF_UFBV", 
			"QF_UFIDL", "QF_UFLIA", "QF_UFLRA", "QF_UFNIA", "QF_UFNRA", "UF", 
			"UFBV", "UFDT", "UFDTLIA", "UFIDL", "UFLIA", "UFLRA", "UFNIA",
	};
	
	private static final String[] DIVISIONS_Mathsat = new String[]{ 
			"QF_ABV", "QF_ALIA", "QF_AUFBV", "QF_AUFLIA", "QF_AX", 
			"QF_BV", 
			"QF_LIA", "QF_LRA", "QF_UF", 
			"QF_UFBV", 
			"QF_UFLIA", "QF_UFLRA",
	};
	
	private static final String[] DIVISIONS_UNSOUND_Mathsat = new String[]{ 
			"QF_BV", 
	};
	
	private static final String[] DIVISIONS_VAMPIRE = new String[]{ 
			"ALIA", "ANIA", 
			"AUFDTLIA",
			"AUFLIA", "AUFLIRA", "AUFNIRA", 
			"LIA", "LRA", "NIA", "NRA", 
			"UF", 
			"UFDT", "UFDTLIA", "UFIDL", "UFLIA", "UFLRA", "UFNIA",
	};
	
	private static final String[] DIVISIONS_Z3 = new String[]{ 
			"ALIA", "ANIA", 
			"AUFLIA", "AUFLIRA", "AUFNIRA", 
			"BV", 
			"LIA", "LRA", "NIA", "NRA", 
			"QF_ABV", 
			"QF_ALIA", "QF_ANIA", "QF_AUFBV", "QF_AUFLIA", "QF_AUFNIA", "QF_AX", 
			"QF_BV", "QF_BVFP",	
			"QF_FP", 
			"QF_IDL", "QF_LIA", "QF_LIRA", "QF_LRA", "QF_NIA", "QF_NIRA", "QF_NRA", "QF_RDL", "QF_UF", 
			"QF_UFBV", 
			"QF_UFIDL", "QF_UFLIA", "QF_UFLRA", "QF_UFNIA", "QF_UFNRA", "UF", 
			"UFBV", 
			"UFIDL", "UFLIA", "UFLRA", "UFNIA",
	};
	
	private static Set<String> ELIGIBLE_DIVISIONS_CVC4;
	private static Set<String> ELIGIBLE_DIVISIONS_Mathsat;
	private static Set<String> ELIGIBLE_DIVISIONS_VAMPIRE;
	private static Set<String> ELIGIBLE_DIVISIONS_Z3;
	private static Set<String>[] VALIDATION_ELIGIBLE;
	
	// @formatter:on
	
	private PostProcessUnsatCoreTrack() {
	}
	
	public static void initializeSolverValidatorMap() {
		SOLVER_VALIDATOR_MAP.put(SOLVER_CVC4, VALIDATION_CVC4);
		SOLVER_VALIDATOR_MAP.put(SOLVER_MATHSAT, VALIDATION_MATHSAT);
		SOLVER_VALIDATOR_MAP.put(SOLVER_Z3, VALIDATION_Z3);
	}
	
	public static void initializeEligibleDivisions() {
		ELIGIBLE_DIVISIONS_CVC4 = new HashSet<>(Arrays.asList(DIVISIONS_CVC4));
		assert ELIGIBLE_DIVISIONS_CVC4.size() == 43;
		ELIGIBLE_DIVISIONS_Mathsat = new HashSet<>(Arrays.asList(DIVISIONS_Mathsat));
		ELIGIBLE_DIVISIONS_Mathsat.removeAll(Arrays.asList(DIVISIONS_UNSOUND_Mathsat));
		assert ELIGIBLE_DIVISIONS_Mathsat.size() == 11;
		ELIGIBLE_DIVISIONS_VAMPIRE = new HashSet<>(Arrays.asList(DIVISIONS_VAMPIRE));
		assert ELIGIBLE_DIVISIONS_VAMPIRE.size() == 17;
		ELIGIBLE_DIVISIONS_Z3 = new HashSet<>(Arrays.asList(DIVISIONS_Z3));
		assert ELIGIBLE_DIVISIONS_Z3.size() == 41;
		VALIDATION_ELIGIBLE = (Set<String>[]) new Set<?>[] { ELIGIBLE_DIVISIONS_CVC4, ELIGIBLE_DIVISIONS_Mathsat, ELIGIBLE_DIVISIONS_VAMPIRE, ELIGIBLE_DIVISIONS_Z3 };
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File(INPUT_FILE_NAME);
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		final List<String> inputColumTitles = input.getColumnTitles();
		initializeEligibleDivisions();
		initializeSolverValidatorMap();
		initializeStatistics();
		final List<String> outputColumTitles = new ArrayList<>(inputColumTitles);
		outputColumTitles.add(VALIDATION_REVISED_CVC4);
		outputColumTitles.add(VALIDATION_REVISED_MATHSAT);
		outputColumTitles.add(VALIDATION_REVISED_VAMPIRE);
		outputColumTitles.add(VALIDATION_REVISED_Z3);
		outputColumTitles.add(REVISED_UC_VALIDATED);
		outputColumTitles.add(REVISED_RESULT_ERRONEOUS);
		outputColumTitles.add(REVISED_REDUCTION);
		
		final ICsvProvider<String> output = new SimpleCsvProvider<>(outputColumTitles);
		final ICsvProvider<String> noValidationOutputConsensus = new SimpleCsvProvider<>(outputColumTitles);
		
		final int rows = input.getTable().size();
		for (int row = 0; row<rows; row++) {
			increment(STATISTICS_JOB_PAIRS);
			final Map<String, String> line = extractInputLineMap(input, inputColumTitles, row);
			final String division = getDivision(line.get("benchmark"));
			assert DIVISIONS.contains(division) : "illegal division";
			assert VALIDATION_ORIGINAL.length == VALIDATION_REVISED.length;
			assert VALIDATION_ORIGINAL.length == VALIDATION_ELIGIBLE.length;
			
			final int reduction;
			final int resultIsErroneous;
			
			if (isCheckSatResultUnknown(line)) {
				resultIsErroneous = 0;
				reduction = 0;
				assert getResultIsErroneous(line) == 0;
				assert getReduction(line) == 0;
			} else if (getCheckSatIsErroneous(line) == 1) {
				increment(STATISTICS_CHECK_SAT_INCORRECT);
				resultIsErroneous = 1;
				reduction = 0;
				assert getResultIsErroneous(line) == 1;
				assert getReduction(line) == 0;
			} else {
				increment(STATISTICS_CHECK_SAT_CORRECT);
				if (!getUcParsable(line)) {
					resultIsErroneous = 0;
					reduction = 0;
					assert getResultIsErroneous(line) == 0;
					assert getReduction(line) == 0;
				} else {
					increment(STATISTICS_PARSABLE_UC);
					constructRevisedValidationResults(line, division);
					final Pair<Boolean, Boolean> validationResult = validateUc(line);
					final boolean ucValidated = validationResult.getFirst();
					final boolean thereWasNoConsensus = validationResult.getSecond();
					if (thereWasNoConsensus) {
						noValidationOutputConsensus.addRow(constructRow(outputColumTitles, line));
					}
					if (ucValidated) {
						increment(STATISTICS_VALIDATED_UC);
						reduction = getAssertsSize(line) - getUcSize(line);
						resultIsErroneous = 0;
						
					} else {
						increment(STATISTICS_INVALID_UC);
						reduction = 0;
						resultIsErroneous = 1;
						assert getResultIsErroneous(line) == 1;
						assert getReduction(line) == 0;
					}
					line.put(REVISED_UC_VALIDATED, String.valueOf(ucValidated));
				}
			}
			line.put(REVISED_RESULT_ERRONEOUS, String.valueOf(resultIsErroneous));
			line.put(REVISED_REDUCTION, String.valueOf(reduction));

			final List<String> values = constructRow(outputColumTitles, line); 
			output.addRow(values);
		}
		System.out.print(printStatistics());
		System.out.println();
		System.out.println("Divisions where sometimes no independent validating solver approved correctness of the unsatisfiable core");
		System.out.println(DIVISIONS_WITHOUT_FULL_UC_APPROVAL.toString());
		System.out.println();
		for (final Map<String, String> line : LINES_WITHOUT_VALIDATION_CONSENSUS) {
			System.out.println(line);	
		}
		writeCsvToFile(output, OUTPUT_FILE_NAME);
		writeCsvToFile(noValidationOutputConsensus, NO_CONSENSUS_OUTPUT_FILE_NAME);
	}

	private static List<String> constructRow(final List<String> outputColumTitles, final Map<String, String> line) {
		final List<String> result = new ArrayList<String>();
		for (final String title : outputColumTitles) {
			final String value = line.get(title);
			if (value == null) {
				result.add("");
			} else {
				result.add(value);
			}
		}
		return result;
	}

	private static void constructRevisedValidationResults(final Map<String, String> line, final String division) {
		for (int i=0; i < VALIDATION_ORIGINAL.length; i++) {
			final String revisedValidationResult;
			if (VALIDATION_ELIGIBLE[i].contains(division)) {
				revisedValidationResult = line.get(VALIDATION_ORIGINAL[i]);
			} else {
				revisedValidationResult = "";
			}
			line.put(VALIDATION_REVISED[i], revisedValidationResult);
		}
	}

	private static Pair<Boolean, Boolean> validateUc(final Map<String, String> line) throws AssertionError {
		int sat = 0;
		int unknown = 0;
		int unsat = 0;
		int unsatFromOtherSolvers = 0;
		boolean selfInvalidated = false;
		for (int i=0; i < VALIDATION_ORIGINAL.length; i++) {
			final boolean sameSolver = VALIDATION_ORIGINAL[i].equals(SOLVER_VALIDATOR_MAP.get(line.get("solver")));
			final String validationValue = line.get(VALIDATION_REVISED[i]); 
			switch (validationValue) {
			case "sat":
				sat++;
				if (sameSolver) {
					selfInvalidated = true;
					increment(STATISTICS_SELFINVALIDATED);
				}
				break;
			case "unsat":
				unsat++;
				if (!sameSolver) {
					unsatFromOtherSolvers++;
				}
				break;
			case "unknown":
				unknown++;
				break;
			case "" :
				break;
			default:
				throw new AssertionError("illegal validation value");
			}
		}
		final boolean ucValidated = !selfInvalidated && (sat <= unsat);
		final boolean validatorDisagreement = (sat > 0 && unsat > 0);
		if (validatorDisagreement) {
			increment(STATISTICS_DISAGREEMENT);
			LINES_WITHOUT_VALIDATION_CONSENSUS.add(line);
		}
		if (unsatFromOtherSolvers == 0) {
			increment(STATISTICS_NOTAPPROVED);
			DIVISIONS_WITHOUT_FULL_UC_APPROVAL.add(getDivision(line.get("benchmark")));
		}
		return new Pair<>(ucValidated, validatorDisagreement);
	}
	
	private static int getUcSize(final Map<String, String> line) {
		final String string = line.get(UC_SIZE);
		return Integer.parseInt(string);
	}
	
	private static int getAssertsSize(final Map<String, String> line) {
		final String string = line.get(ASSERTS_SIZE);
		return Integer.parseInt(string);
	}
	
	private static int getReduction(final Map<String, String> line) {
		final String string = line.get(REDUCTION);
		return Integer.parseInt(string);
	}
	
	private static int getResultIsErroneous(final Map<String, String> line) {
		final String string = line.get(RESULT_ERRONEOUS);
		return Integer.parseInt(string);
	}
	
	private static int getCheckSatIsErroneous(final Map<String, String> line) {
		final String string = line.get(CHECK_SAT_IS_ERRONEOUS);
		return Integer.parseInt(string);
	}
	
	private static boolean getUcParsable(final Map<String, String> line) {
		final String string = line.get(UC_PARSABLE);
		return Boolean.parseBoolean(string);
	}
	
	private static boolean getUcValidated(final Map<String, String> line) {
		final String string = line.get(UC_VALIDATED);
		return Boolean.parseBoolean(string);
	}

	private static boolean isCheckSatResultUnknown(final Map<String, String> line) {
		final String string = line.get(CHECK_SAT_RESULT);
		return CHECK_SAT_RESULT_VALUE_UNKNOWN.equals(string);
	}
	
	
	
	


	private static Map<String, String> extractInputLineMap(final ICsvProvider<String> input, final List<String> ct,
			final int i) {
		final Map<String, String> inputLineMap = new LinkedHashMap<>();
		final List<String> row = input.getRow(i);
		int offset = 0;
		for (final String columnTitle : ct) {
			inputLineMap.put(columnTitle, row.get(offset));
			offset++;
		}
		return inputLineMap;
	}
	
	public static String getDivision(final String benchmarkString) {
		final String withoutPrefix = benchmarkString.replaceFirst("Competition - Unsat-Core Track/", "");
		final int index = withoutPrefix.indexOf("/");
		final String result = withoutPrefix.substring(0, index);
		return result;
	}
	

	// copied from Christian
	private static void writeCsvToFile(final ICsvProvider<String> csv, final String fileName) {
		final StringBuilder predefinedBuilder = new StringBuilder();
		final StringBuilder builder = csv.toCsv(predefinedBuilder, ",", true);
		final File file = new File(fileName);
		try (BufferedWriter writer = new BufferedWriter(new FileWriter(file))) {
			writer.append(builder);
		} catch (final IOException e) {
			System.err.println("Writing file " + fileName + " failed.");
			e.printStackTrace();
		}
	}
	
}
