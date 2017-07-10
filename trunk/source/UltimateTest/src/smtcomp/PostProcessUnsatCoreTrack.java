package smtcomp;

import java.io.File;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;

/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class PostProcessUnsatCoreTrack {
	private static final String INPUT_FILE_NAME = "/home/matthias/ultimate/Job21979_info.csv";

	
	private static final String VALIDATION_CVC4 = "validation-check-sat-result_cvc4";
	private static final String VALIDATION_MATHSAT = "validation-check-sat-result_mathsat";
	private static final String VALIDATION_VAMPIRE = "validation-check-sat-result_vampire";
	private static final String VALIDATION_Z3 = "validation-check-sat-result_z3";

	private static final String REVISED_VALIDATION_CVC4 = "REVISED_validation-check-sat-result_cvc4";
	private static final String REVISED_VALIDATION_MATHSAT = "REVISED_validation-check-sat-result_mathsat";
	private static final String REVISED_VALIDATION_VAMPIRE = "REVISED_validation-check-sat-result_vampire";
	private static final String REVISED_VALIDATION_Z3 = "REVISED_validation-check-sat-result_z3";
	
	private static final String UC_VALIDATED = "unsat-core-validated"; // true or false
	private static final String UC_SIZE = "size-unsat-core";
	
	private static final String ASSERTS_SIZE = "number-of-assert-commands";
	private static final String CHECK_SAT_IS_ERRONEOUS = "check-sat-result-is-erroneous"; // 0 or 1
	private static final String REDUCTION = "reduction";
	private static final String RESULT_ERRONEOUS = "result-is-erroneous"; // 0 or 1
	private static final String UC_PARSABLE = "parsable-unsat-core"; // true or false
	
	
	
	

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
	
	
	private PostProcessUnsatCoreTrack() {
	}
	
	public static void initializeEligibleDivisions() {
		ELIGIBLE_DIVISIONS_CVC4 = new HashSet<>(Arrays.asList(DIVISIONS_CVC4));
		ELIGIBLE_DIVISIONS_Mathsat = new HashSet<>(Arrays.asList(DIVISIONS_Mathsat));
		ELIGIBLE_DIVISIONS_Mathsat.removeAll(Arrays.asList(DIVISIONS_UNSOUND_Mathsat));
		ELIGIBLE_DIVISIONS_VAMPIRE = new HashSet<>(Arrays.asList(DIVISIONS_VAMPIRE));
		ELIGIBLE_DIVISIONS_Z3 = new HashSet<>(Arrays.asList(DIVISIONS_Z3));
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File(INPUT_FILE_NAME);
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		final List<String> rh = input.getRowHeaders();
		final List<String> ct = input.getColumnTitles();
		final int rows = input.getTable().size();
		for (int i = 0; i<rows; i++) {
			final Map<String, String> inputLineMap = extractInputLineMap(input, ct, i);
			final String division = getDivision(inputLineMap.get("benchmark"));
			assert DIVISIONS.contains(division) : "illegal division";
			final String revised_validation_cvc4 = null;
			inputLineMap.toString();
			initializeEligibleDivisions();
			final Set<String> lol = ELIGIBLE_DIVISIONS_Mathsat;
			lol.toString();
		}
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
	
}
