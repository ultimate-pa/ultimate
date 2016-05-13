package de.uni_freiburg.informatik.ultimate.automata.tree.operators;

import java.util.Set;

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

public class Complement<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final AutomataLibraryServices m_Services;
	private final ILogger m_Logger;
	
	private final TreeAutomatonBU<LETTER, STATE> m_Operand;
	private TreeAutomatonBU<LETTER, NamedState<Set<MyState<STATE>>>> m_Result;
	private final StateFactory<STATE> m_StateFactory;
	

	public Complement(AutomataLibraryServices services, TreeAutomatonBU<LETTER, STATE> operand) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_StateFactory = m_Operand.getStateFactory();
		m_Logger.info(startMessage());
		ConverterToFTA<LETTER, STATE> converter = new ConverterToFTA<LETTER, STATE>();
		GenFTA<MySymbol<LETTER>, NamedState<Set<MyState<STATE>>>> gen = GenFTAOps.complement(converter.convertITreeToFTA(m_Operand));
		ConverterFTAToTree<LETTER, NamedState<Set<MyState<STATE>>>> reverseConverter = new ConverterFTAToTree<>();
		m_Result = reverseConverter.convertToTree(gen);
		m_Logger.info(exitMessage());
	}

	@Override
	public String operationName() {
		return "Complement";
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
	public TreeAutomatonBU<LETTER, NamedState<Set<MyState<STATE>>>> getResult() throws AutomataLibraryException {
		return m_Result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return false;
	}

}
