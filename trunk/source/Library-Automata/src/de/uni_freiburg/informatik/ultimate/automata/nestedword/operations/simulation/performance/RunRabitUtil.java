package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

public class RunRabitUtil {

	/**
	 * File representing the working environment.
	 */
	public static final File ENVIRONMENT = new File(new File(System.getProperty("user.home"), "Desktop"), "rabit");
	/**
	 * The maximal heap size in gigabyte to use for the Rabit tool.
	 */
	public static final int MAX_HEAP_SIZE_GB = 2;
	/**
	 * The minimal heap size in gigabyte to use for the Rabit tool.
	 */
	public static final int MIN_HEAP_SIZE_GB = 2;
	/**
	 * Name of the tool to use.
	 */
	public static final String TOOL = ENVIRONMENT.getAbsolutePath() + "/rabit.jar";

	public static final String ARROW = "->";
	public static final String COMMA = ",";

	public static final String NOT_INCLUDED = "Not included";

	/**
	 *
	 * Name of the file A
	 */
	public static final String A_FILE = ENVIRONMENT.getAbsolutePath() + "/A.ba";

	/**
	 *
	 * Name of the file B
	 */
	public static final String B_FILE = ENVIRONMENT.getAbsolutePath() + "/B.ba";

	private RunRabitUtil() {
		// utility class
	}

	/**
	 * Executes the Buechic tool on a given automaton using the given arguments.
	 *
	 * @param automaton
	 *            Automaton to execute Buechic on
	 * @param arguments
	 *            Arguments to pass to the Buechic tool
	 * @return The standard output produced by the tool
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static Boolean executeRabit(final AutomataLibraryServices services) throws Exception {

		final Runtime rt = Runtime.getRuntime();
		String command = "java";
		command += " -Xms" + MIN_HEAP_SIZE_GB + "g -Xms" + MIN_HEAP_SIZE_GB + "G";
		command += " -Xmx" + MAX_HEAP_SIZE_GB + "g -Xmx" + MAX_HEAP_SIZE_GB + "G";
		command += " -jar";
		command += " " + TOOL;
		command += " " + A_FILE + " " + B_FILE;
		command += " -fast";
		final Process proc = rt.exec(command);
		System.out.println(command);

		// proc.waitFor();
		// System.out.println("while loop");
		while (true) {
			if (!proc.isAlive()) {
				System.out.println("Rabit exit normally");
				break;
			}
			if (!services.getProgressAwareTimer().continueProcessing()) {
				System.err.println("Rabit Time out exception");
				// proc.destroy();
				proc.destroyForcibly();
				return null;
			}
		}

		final BufferedReader reader = new BufferedReader(new InputStreamReader(proc.getInputStream()));
		String line = null;
		boolean result = true;
		while ((line = reader.readLine()) != null) {
			if (line.contains(NOT_INCLUDED)) {
				result = false;
			}
			System.out.println(line);
		}

		return result;

	}

	/**
	 * Execute Buechic in command line
	 */
	public static <LETTER, STATE> Boolean executeRabit(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOp,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOp, final AutomataLibraryServices services)
			throws Exception {
		final int[] num = { 0 };
		// give every letter a symbol
		final Map<LETTER, String> letter2StrMap = new HashMap<>();
		final Set<LETTER> letters = new HashSet<>();
		for (final LETTER letter : fstOp.getAlphabet()) {
			letter2StrMap.put(letter, "a" + num[0]);
			letters.add(letter);
			num[0]++;
		}

		for (final LETTER letter : sndOp.getAlphabet()) {
			if (letters.contains(letter)) {
				continue;
			}
			letter2StrMap.put(letter, "a" + num[0]);
			num[0]++;
		}

		writeFile(A_FILE, fstOp, letter2StrMap);
		writeFile(B_FILE, sndOp, letter2StrMap);
		// file
		return executeRabit(services);
	}

	private static <LETTER, STATE> void writeFile(final String file,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> op, final Map<LETTER, String> letter2StrMap)
			throws IOException {
		// now we input this automata in a file
		final Map<STATE, String> state2Str = new HashMap<>();
		final Map<String, STATE> str2State = new HashMap<>();

		final Iterable<STATE> states = op.getInitialStates();
		final StringBuilder sb = new StringBuilder();

		final int[] num = { 0 };
		// print initial state
		for (final STATE st : states) {
			sb.append("s" + num[0] + "\n");
			addState(state2Str, str2State, st, num);
		}

		// traverse the whole state space
		final Queue<STATE> queue = new LinkedList<>();
		final Set<STATE> visited = new HashSet<>();
		final Set<STATE> finals = new HashSet<>();

		for (final STATE st : states) {
			queue.add(st);
		}

		// traverse the state space
		while (!queue.isEmpty()) {
			final STATE state = queue.poll();
			addState(state2Str, str2State, state, num);
			visited.add(state);
			if (op.isFinal(state)) {
				finals.add(state);
			}
			// print all successors
			final Iterable<OutgoingInternalTransition<LETTER, STATE>> successors = op.internalSuccessors(state);
			for (final OutgoingInternalTransition<LETTER, STATE> trans : successors) {
				final STATE succ = trans.getSucc();
				addState(state2Str, str2State, succ, num);
				if (!visited.contains(succ)) {
					queue.add(succ);
				}
				sb.append(letter2StrMap.get(trans.getLetter()) + "," + state2Str.get(state) + "->" + state2Str.get(succ)
						+ "\n");
			}
		}

		for (final STATE f : finals) {
			sb.append(state2Str.get(f) + "\n");
		}

		final File inFile = new File(file);
		try (final FileWriter writer = new FileWriter(inFile)) {
			writer.write(sb.toString());
		}

	}

	private static <LETTER, STATE> void addState(final Map<STATE, String> state2Str, final Map<String, STATE> str2State,
			final STATE state, final int[] num) {
		if (state2Str.get(state) == null) {
			state2Str.put(state, "s" + num[0]);
			str2State.put("s" + num[0], state);
			num[0]++;
		}
	}

	/**
	 * Collects all BA-automata from a given directory, executes the RABIT tool on them and finally aggregates and
	 * converts the results to a format used by Ultimate.
	 *
	 * @param args
	 *            Not supported
	 * @throws IOException
	 *             If an I/O-Exception occurred.
	 */
	public static void main(final String[] args) throws Exception {
		System.out.println("Start");
		// System.out.println("result: " + executeRabit());
		System.out.println("Terminated");
	}

}
