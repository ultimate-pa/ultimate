package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.sql.Timestamp;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.SimulationOrMinimizationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Provides utility methods for converting benchmark data provided by the Buechic tool to formats used by Ultimates
 * simulation benchmark framework.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @author Yong Li {@literal <liyong460@gmail.com>}
 */
public final class BuechicUtil {

	/**
	 * File representing the working environment.
	 */
	public static final File ENVIRONMENT =
			new File(new File(System.getProperty("user.home"), "Desktop"), "buechic");
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
	public static final String TOOL = ENVIRONMENT.getAbsolutePath() + "/buechic.jar";

	public static final String ARROW = "->";
	public static final String COMMA = ",";
	
	/**
	 * 
	 * Name of the file output
	 */
	public static final String OUT_FILE = ENVIRONMENT.getAbsolutePath() + "/out.ba";
	/**
	 * 
	 * Name of the file input
	 */
	public static final String IN_FILE = ENVIRONMENT.getAbsolutePath() + "/in.ba";

	private BuechicUtil() {
		// utility class
	}
	
	private static List<String> outputFile(String file) throws IOException {

		final BufferedReader reader = new BufferedReader(new FileReader(file));
		
		final List<String> outputLines = new LinkedList<>();
		String line = null;
		while((line = reader.readLine()) != null) {
//			System.out.println("out: " + line);
			outputLines.add(line);
		}
		reader.close();
		
		return outputLines;
		
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
	public static List<String> executeBuechic(File automaton, final String arguments) throws Exception {
		Timestamp timestamp = new Timestamp(System.currentTimeMillis());
//		String fileStr = OUT_FILE + timestamp.getTime();
		String fileStr = OUT_FILE;
		File file = new File(fileStr);
		if(file.exists()) {
			file.deleteOnExit();
			System.out.println("Delete");
		}
		
		final Runtime rt = Runtime.getRuntime();
		String command = "java";
		command += " -Xms" + MIN_HEAP_SIZE_GB + "g -Xms" + MIN_HEAP_SIZE_GB + "G";
		command += " -Xmx" + MAX_HEAP_SIZE_GB + "g -Xmx" + MAX_HEAP_SIZE_GB + "G";
		command += " -jar";
		command += " " + TOOL;
		command += " " + automaton.getAbsolutePath() + "";
		command += " " + arguments + " -out " + fileStr;
		final Process proc = rt.exec(command);
		System.out.println(command);
//		final BufferedReader reader2 = new  BufferedReader(new InputStreamReader(proc.getErrorStream()));
//		String line2 = null;
//		while((line2 = reader2.readLine()) != null) {
//			System.out.println(line2);
//		}
		proc.waitFor();
		List<String> outputLines = outputFile(fileStr);
		
		return outputLines;
	}
	/**
	 * Execute Buechic in command line 
	 * */
	public static  <LETTER, STATE> List<String> executeBuechic(Map<String, LETTER> str2LetterMap
			, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws Exception {
		int[] num = {0};
		// give every letter a symbol
		Map<LETTER, String> letter2StrMap = new HashMap<>();
		for(LETTER letter : operand.getAlphabet()) {
			letter2StrMap.put(letter, "a" + num[0]);
			str2LetterMap.put("a" + num[0], letter);
			num[0] ++;
		}
		
		Map<STATE, String> state2Str = new HashMap<>();
		Map<String, STATE> str2State = new HashMap<>();
		
		Iterable<STATE> states = operand.getInitialStates();
		
		// for states 
		num[0] = 0;
		StringBuilder sb = new StringBuilder();
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
			if(operand.isFinal(state)) {
				finals.add(state);
			}
			// print all successors
			Iterable<OutgoingInternalTransition<LETTER, STATE>>
			 successors = operand.internalSuccessors(state);
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
		
		// now we input automaton into Buechic
		inputFile(sb.toString());
//        System.out.println("in: \n" + sb.toString());
//	    for(String str : outputFile(IN_FILE)) {
//	    	System.out.println("ot: " + str);
//	    }
	    // file
		return executeBuechic(new File(IN_FILE), " -table -syntactic");
	}
	
	private static void inputFile(String content) throws IOException {
		File inFile = new File(IN_FILE);
		FileWriter writer = new FileWriter(inFile);
	    writer.write(content);
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

		List<String> outs = executeBuechic(new File("/home/liyong/Desktop/buechic/input.ba"), " -table -syntactic");
        
		for(String line : outs) {
			System.out.println(line);
		}
		System.out.println("Terminated");
		String nn = "a,90->29";
		String[] pre = nn.split(",");
		for(String p : pre) {
			System.out.println(p);
		}
		System.out.println("------------");
		String k = pre[1];
		String[] mm = k.split("->");
		for(String p : mm) {
			System.out.println(p);
		}
	}

}

