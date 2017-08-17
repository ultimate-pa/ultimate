package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.sql.Timestamp;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.SimulationOrMinimizationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class RunRabitUtil {


	/**
	 * File representing the working environment.
	 */
	public static final File ENVIRONMENT =
			new File(new File(System.getProperty("user.home"), "Desktop"), "rabit");
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
		
//		proc.waitFor();
//		System.out.println("while loop");
		while(true) {
			if(! proc.isAlive()) {
				System.out.println("Rabit exit normally");
				break;
			}
			if(! services.getProgressAwareTimer().continueProcessing()) {
				System.err.println("Rabit Time out exception");
//				proc.destroy();
				proc.destroyForcibly();
				return null;
			}
		}
		
		final BufferedReader reader = new  BufferedReader(new InputStreamReader(proc.getInputStream()));
		String line = null;
		boolean result = true;
		while((line = reader.readLine()) != null) {
			if(line.contains(NOT_INCLUDED)) {
				result = false;
			}
			System.out.println(line);
		}

		return result;

	}
	/**
	 * Execute Buechic in command line 
	 * */
	public static  <LETTER, STATE> Boolean executeRabit(
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOp
		  , final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOp,
		  final AutomataLibraryServices services) throws Exception {
		int[] num = {0};
		// give every letter a symbol
		Map<LETTER, String> letter2StrMap = new HashMap<>();
 		Set<LETTER> letters = new HashSet<>();
		for(LETTER letter : fstOp.getAlphabet()) {
			letter2StrMap.put(letter, "a" + num[0]);
			letters.add(letter);
			num[0] ++;
		}
		
		for(LETTER letter : sndOp.getAlphabet()) {
			if(letters.contains(letter)) continue;
			letter2StrMap.put(letter, "a" + num[0]);
			num[0] ++;
		}
		
		writeFile(A_FILE, fstOp, letter2StrMap);
		writeFile(B_FILE, sndOp, letter2StrMap);
	    // file
		return executeRabit(services);
	}
	
	
	
	private static <LETTER, STATE> void writeFile(String file
			, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> op,
			Map<LETTER, String> letter2StrMap) throws IOException {
		// now we input this automata in a file
		Map<STATE, String> state2Str = new HashMap<>();
		Map<String, STATE> str2State = new HashMap<>();
		
		Iterable<STATE> states = op.getInitialStates();
		StringBuilder sb = new StringBuilder();
		
		int[] num = {0};
		// print initial state
		for(STATE st : states) {
			sb.append("s" + num[0] + "\n" );
			addState(state2Str, str2State, st, num);
		}
		
		
		// traverse the whole state space
		Queue<STATE> queue = new LinkedList<>();
		Set<STATE> visited = new HashSet<>();
		Set<STATE> finals = new HashSet<>();
		
		for(STATE st : states) {
			queue.add(st);
		}
		
		// traverse the state space
		while(! queue.isEmpty()) {
			STATE state = queue.poll();
			addState(state2Str, str2State, state, num);
			visited.add(state);
			if(op.isFinal(state)) {
				finals.add(state);
			}
			// print all successors
			Iterable<OutgoingInternalTransition<LETTER, STATE>>
			 successors = op.internalSuccessors(state);
			for(OutgoingInternalTransition<LETTER, STATE> trans : successors) {
				STATE succ = trans.getSucc();
				addState(state2Str, str2State, succ, num);
				if(! visited.contains(succ)) {
					queue.add(succ);
				}
				sb.append(letter2StrMap.get(trans.getLetter()) + "," + state2Str.get(state) + "->" + state2Str.get(succ) + "\n");
			}
		}
		
		for(STATE f : finals) {
			sb.append(state2Str.get(f) + "\n");
		}
		
		File inFile = new File(file);
		FileWriter writer = new FileWriter(inFile);
	    writer.write(sb.toString());
        writer.close();
        
	}
	
	private static <LETTER, STATE>  void addState(Map<STATE, String> state2Str, Map<String, STATE> str2State
			, STATE state, int[] num) {
		if(state2Str.get(state) == null) {
			state2Str.put(state, "s" + num[0]);
			str2State.put("s" + num[0], state);
			num[0] ++ ;
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
//		System.out.println("result: " + executeRabit());
		System.out.println("Terminated");
	}
	
}
