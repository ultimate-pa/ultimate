package de.uni_freiburg.informatik.ultimate.automata.tree.operators;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.operators.Converter.MyState;
import de.uni_freiburg.informatik.ultimate.automata.tree.operators.Converter.MySymbol;
import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;
import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps;
import de.uni_muenster.cs.sev.lethal.utils.Pair;

public class Intersect<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private final AutomataLibraryServices m_Services;
	private final ILogger m_Logger;

	private final TreeAutomatonBU<LETTER, STATE> m_FstOperand;
	private final TreeAutomatonBU<LETTER, STATE> m_SndOperand;
	private final TreeAutomatonBU<LETTER, NamedState<Pair<MyState<STATE>, MyState<STATE>>>> m_Result;
	private final StateFactory<STATE> m_StateFactory;

	public Intersect(AutomataLibraryServices services, TreeAutomatonBU<LETTER, STATE> fstOperand,
			TreeAutomatonBU<LETTER, STATE> sndOperand) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_FstOperand = fstOperand;
		m_SndOperand = sndOperand;
		m_StateFactory = m_FstOperand.getStateFactory();
		m_Logger.info(startMessage());
		ConverterToFTA<LETTER, STATE> converter = new ConverterToFTA<LETTER, STATE>();
		GenFTA<MySymbol<LETTER>, NamedState<Pair<MyState<STATE>, MyState<STATE>>>> gen = GenFTAOps
				.intersectionBU(converter.convertITreeToFTA(m_FstOperand), converter.convertITreeToFTA(m_SndOperand));
		ConverterFTAToTree<LETTER, NamedState<Pair<MyState<STATE>, MyState<STATE>>>> reverseConverter = new ConverterFTAToTree<>();
		m_Result = reverseConverter.convertToTree(gen);
		m_Logger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "Intersection";
	}

	@Override
	public String startMessage() {
		return "Starting " + operationName();
	}

	@Override
	public String exitMessage() {
		return "Finishing " + operationName();
	}

	@Override
	public TreeAutomatonBU<LETTER, NamedState<Pair<MyState<STATE>, MyState<STATE>>>> getResult()
			throws AutomataLibraryException {
		return m_Result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return false;
	}
	public static void main(String[] args) {
		TreeAutomatonBU<String, String> tree = new TreeAutomatonBU<>();
		String[] letters = {"T", "F", "Nil", "cons"};
		String list = "List", bool = "Bool";
		tree.addState(bool); tree.addState(list);
		tree.addFinalState(list);
		tree.addInitialState(bool);tree.addInitialState(list);
		ArrayList<String> st = new ArrayList<String>();
		st.add(bool); st.add(list);
		tree.addRule(letters[3], st, list);
		tree.addRule(letters[0], new ArrayList<String>(), bool);
		tree.addRule(letters[1], new ArrayList<String>(), bool);
		tree.addRule(letters[2], new ArrayList<String>(), list);
		
		
		ConverterToFTA<String, String> converter = new ConverterToFTA<String, String>();
		GenFTA<MySymbol<String>, MyState<String>> gen = converter.convertITreeToFTA(tree);
		System.out.println(gen.rulesToString());
		ConverterFTAToTree<String, MyState<String>> reverseConverter = new ConverterFTAToTree<>();
	
		TreeAutomatonBU<String, MyState<String>> tt = reverseConverter.convertToTree(gen);
		
		System.out.printf("%s\nX\n%s\n", tree.DebugString(), tt.DebugString());
	}
}
