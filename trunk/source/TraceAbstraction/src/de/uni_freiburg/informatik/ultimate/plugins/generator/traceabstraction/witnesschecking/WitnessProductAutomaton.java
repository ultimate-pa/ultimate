package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;

public class WitnessProductAutomaton implements INestedWordAutomatonSimple<CodeBlock, IPredicate> {
	private SmtManager m_SmtManager;
	INestedWordAutomatonSimple<CodeBlock, IPredicate> m_ControlFlowAutomaton;
	INestedWordAutomatonSimple<WitnessAutomatonLetter, WitnessAutomatonState> m_WitnessAutomaton;
	
	NestedMap2<IPredicate, WitnessAutomatonState, ProductState> m_Cfg2Witness2Result;
	private IPredicate m_EmptyStackState;
	
	private class ProductState {
		private final IPredicate m_CfgAutomatonState;
		private final WitnessAutomatonState m_WitnessAutomatonState;
		private ISLPredicate m_ResultState;

		
		public ProductState(IPredicate cfgAutomatonState,
				WitnessAutomatonState witnessAutomatonState) {
			super();
			m_CfgAutomatonState = cfgAutomatonState;
			m_WitnessAutomatonState = witnessAutomatonState;
			m_ResultState = constructNewResultState(cfgAutomatonState, witnessAutomatonState);
		}
		private ISLPredicate constructNewResultState(IPredicate cfgAutomatonState, WitnessAutomatonState witnessAutomatonState) {
			return m_SmtManager.newTrueSLPredicate(((ISLPredicate) cfgAutomatonState).getProgramPoint()); 
		}
		
		public IPredicate getCfgAutomatonState() {
			return m_CfgAutomatonState;
		}
		public WitnessAutomatonState getWitnessAutomatonState() {
			return m_WitnessAutomatonState;
		}
		public ISLPredicate getResultState() {
			return m_ResultState;
		}
	}
	
	private ProductState getOrConstructProductState(
			IPredicate cfgAutomatonState, 
			WitnessAutomatonState witnessAutomatonState) {
		ProductState productState = m_Cfg2Witness2Result.get(cfgAutomatonState, witnessAutomatonState);
		if (productState == null) {
			productState = new ProductState(cfgAutomatonState, witnessAutomatonState);
			m_Cfg2Witness2Result.put(cfgAutomatonState, witnessAutomatonState, productState);
		}
		return productState;
	}

	@Override
	public Set<CodeBlock> getAlphabet() {
		throw new UnsupportedOperationException("has three alphabets");
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String sizeInformation() {
		return null;
	}

	@Override
	public Set<CodeBlock> getInternalAlphabet() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<CodeBlock> getCallAlphabet() {
		return m_ControlFlowAutomaton.getCallAlphabet();
	}

	@Override
	public Set<CodeBlock> getReturnAlphabet() {
		return m_ControlFlowAutomaton.getReturnAlphabet();
	}

	@Override
	public StateFactory<IPredicate> getStateFactory() {
		return m_ControlFlowAutomaton.getStateFactory();
	}

	@Override
	public IPredicate getEmptyStackState() {
		return m_EmptyStackState;
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isInitial(IPredicate state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFinal(IPredicate state) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Set<CodeBlock> lettersInternal(IPredicate state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<CodeBlock> lettersCall(IPredicate state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Set<CodeBlock> lettersReturn(IPredicate state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state, CodeBlock letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state, CodeBlock letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSucccessors(
			IPredicate state, IPredicate hier, CodeBlock letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSuccessorsGivenHier(
			IPredicate state, IPredicate hier) {
		// TODO Auto-generated method stub
		return null;
	}

}
