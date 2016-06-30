package de.uni_freiburg.informatik.ultimate.automata.tree.lethaloperators;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.lethaloperators.Converter.MyState;
import de.uni_freiburg.informatik.ultimate.automata.tree.lethaloperators.Converter.MySymbol;
import de.uni_muenster.cs.sev.lethal.states.NamedState;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTA;
import de.uni_muenster.cs.sev.lethal.treeautomata.generic.GenFTAOps;

/**
 * Complemention operation from Lethal for TreeAutomatons.
 * 
 * 
 * @param <LETTER> is the type of the alphabet.
 * @param <STATE> is the type of the states.
 * 
 * @author Mostafa M.A.
 */
public class LethalComplement<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final AutomataLibraryServices m_Services;
	private final Logger m_Logger;
	
	private final TreeAutomatonBU<LETTER, STATE> m_Operand;
	private final TreeAutomatonBU<LETTER, NamedState<Set<MyState<STATE>>>> m_Result;
	private final StateFactory<STATE> m_StateFactory;
	

	public LethalComplement(AutomataLibraryServices services, TreeAutomatonBU<LETTER, STATE> operand) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_StateFactory = m_Operand.getStateFactory();
		m_Logger.info(startMessage());
		ConverterTreeToLethalFTA<LETTER, STATE> converter = new ConverterTreeToLethalFTA<LETTER, STATE>();
		GenFTA<MySymbol<LETTER>, NamedState<Set<MyState<STATE>>>> gen = GenFTAOps.complement(converter.convertITreeToFTA(m_Operand));
		ConverterLethalFTAToTree<LETTER, NamedState<Set<MyState<STATE>>>> reverseConverter = new ConverterLethalFTAToTree<>();
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
