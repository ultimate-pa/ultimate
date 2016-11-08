import java.io.BufferedReader;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Quick and dirty script to extract the results from an Ultimate's Trace Abstraction output.
 * <p>
 * Usage (after compilation):
 * <pre>
 * java   ResultExtractor.class   C_FILE   ULTIMATE_LOG_FILE
 * </pre>
 * <p>
 * This script outputs a comma-separated table (.csv).
 * The table has no header. A suitable header would be:
 * <pre>
 * Error's program line number,   error code,   Ultimate's result (reachable/unreachable),   Trace
 * </pre>
 * {@code Trace} is only present for reachable errors and may span more than one column.
 * The trace contains the return values of {@code __VERIFIER_nondet_int()} in sequential order.
 * We can replace {@code __VERIFIER_nondet_int()} by {@code scanf()} and type in the values to check
 * the actual reachability.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class ResultExtractor {

	public static void main(String[] args) {
		if (args.length != 2) {
			System.out.println("usage: ");
			System.out.println("       java   ResultExtractor.class   C_FILE   ULTIMATE_LOG_FILE");
			System.exit(1);
		}
		String pathToCFile = args[0];
		String pathToUltimateLog = args[1];
		ResultExtractor extractor = new ResultExtractor();
		extractor.readFileLineByLine(pathToCFile, extractor::parseLineCFile);
		extractor.readFileLineByLine(pathToUltimateLog, extractor::parseLineUltimateLog);
		extractor.printTable();
	}

	// -------------------------

	List<TableRow> table = new ArrayList<>(100);

	void readFileLineByLine(String pathToFile, LineParser lineParser) {
		try (BufferedReader br = new BufferedReader(new FileReader(pathToFile))) {
			String line;
			int lineNumber = 0;
			while ((line = br.readLine()) != null) {
				++lineNumber;
				lineParser.parse(lineNumber, line);
		    }
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	private static final Pattern regexErrorCall = Pattern.compile("__VERIFIER_error\\((-?[0-9]+)\\)");
	private static final int regexGroupErrorCode = 1;
	private static final Pattern regexReachable = Pattern.compile("\\[Line: ([0-9]+)\\]: a call of __VERIFIER_error\\(\\) is reachable");
	private static final Pattern regexUnreachable = Pattern.compile("\\[Line: ([0-9]+)\\]: call of __VERIFIER_error\\(\\) unreachable");
	private static final int regexGroupProgramLineNumber = 1;

	void parseLineCFile(int programLineNumber, String programLine) {
		Matcher matcher = regexErrorCall.matcher(programLine);
		if (matcher.find()) {
			table.add(new TableRow(programLineNumber, Integer.valueOf(matcher.group(regexGroupErrorCode))));
		}
	}
	
	Consumer<String> logParseMode = this::skipToResultsSection;
	void parseLineUltimateLog(int logLineNumber, String logLine) {
		logParseMode.accept(logLine);
	}
	
	void skipToResultsSection(String logLine) {
		if (logLine.endsWith("--- Results ---")) {
			logParseMode = this::goToNextResult;
		}
	}

	void goToNextResult(String logLine) {
		// TODO remove code duplicates
		Matcher matcherUnreachable = regexUnreachable.matcher(logLine);
		if (matcherUnreachable.find()) {
			int programLineNumber = Integer.parseInt(matcherUnreachable.group(regexGroupProgramLineNumber));
			TableRow tableRow = getTableRow(programLineNumber);
			assertAvailableAndUnknown(tableRow);
			tableRow.reachability = Reachability.UNREACHABLE;
		} else {
			Matcher matcherReachable = regexReachable.matcher(logLine);
			if (matcherReachable.find()) {
				int programLineNumber = Integer.parseInt(matcherReachable.group(regexGroupProgramLineNumber));
				TableRow tableRow = getTableRow(programLineNumber);
				assertAvailableAndUnknown(tableRow);
				tableRow.reachability = Reachability.REACHABLE;
				logParseMode = logLn -> goToNondetAssignOrEndOfTrace(tableRow, logLn);
			}
		}
	}
	
	private void assertAvailableAndUnknown(TableRow row) {
		if (row == null) {
			throw new AssertionError("Ultimate referenced unknown error location");
		} else if (row.reachability != Reachability.UNKNOWN) {
			throw new AssertionError("Ultimate log contained conflicting results");
		}
	}
	
	private static final Pattern regexNondetVarName = Pattern.compile("(\\S+) = __VERIFIER_nondet_int\\(\\)$");
	private static final int regexGroupNondetVarName = 1;
	void goToNondetAssignOrEndOfTrace(TableRow tableRow, String logLine) {
		if (logLine.startsWith("[L" + tableRow.programLineNumber + "]")) {
			logParseMode = this::goToNextResult;
			return;
		}
		
		Matcher matcherNondetVarName = regexNondetVarName.matcher(logLine);
		if (matcherNondetVarName.find()) {
			String nondetVarName = matcherNondetVarName.group(regexGroupNondetVarName);
			logParseMode = logLn -> parseNondetValue(tableRow, nondetVarName, logLn);
		}
	}
	
	private static final Pattern regexTraceValues = Pattern.compile("^\\s*VAL\\s");
	void parseNondetValue(TableRow tableRow, String nondetVarName, String logLine) {
		if (regexTraceValues.matcher(logLine).find()) {
			Pattern regexVarVal = Pattern.compile("\\[.*" + Pattern.quote(nondetVarName) + "=(-?[0-9]+)[,\\]]");
			Matcher matcherVarVal = regexVarVal.matcher(logLine);
			if (!matcherVarVal.find()) {
				throw new IllegalArgumentException("Missing value for non-deterministic variable: " + nondetVarName + " (program line " + tableRow.programLineNumber + ")");
			}
			int nondetValue = Integer.parseInt(matcherVarVal.group(1));
			tableRow.traceInput.add(nondetValue);
			logParseMode = logLn -> goToNondetAssignOrEndOfTrace(tableRow, logLn);
		}
	}
	
	private TableRow getTableRow(int programLineNumber) {
		for (TableRow row : table) {
			if (row.programLineNumber == programLineNumber) {
				return row;
			}
		}
		return null;
	}

	void printTable() {
		for (TableRow row : table) {
			System.out.println(row);
		}
	}
}

class TableRow {

	public static final String DELIMITER = ",";

	int programLineNumber;
	int errorCode;
	Reachability reachability = Reachability.UNKNOWN;
	List<Integer> traceInput = new ArrayList<>(); 
	
	public TableRow(int programLineNumber, int errorCode) {
		this.programLineNumber = programLineNumber;
		this.errorCode = errorCode;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(programLineNumber).append(DELIMITER).append(errorCode).append(DELIMITER).append(reachability);
		for (int in : traceInput) {
			sb.append(DELIMITER).append(in);
		}
		return sb.toString();
	}
}

enum Reachability {
	UNKNOWN, UNREACHABLE, REACHABLE;
}

@FunctionalInterface
interface LineParser {
    public void parse(int lineNumber, String line);
}