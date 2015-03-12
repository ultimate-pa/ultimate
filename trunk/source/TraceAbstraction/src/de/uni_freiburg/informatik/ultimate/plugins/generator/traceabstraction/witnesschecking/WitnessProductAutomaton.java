package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class WitnessProductAutomaton implements INestedWordAutomatonSimple<CodeBlock, IPredicate> {
	private final  SmtManager m_SmtManager;
	private final INestedWordAutomatonSimple<CodeBlock, IPredicate> m_ControlFlowAutomaton;
	private final INestedWordAutomatonSimple<WitnessAutomatonLetter, WitnessNode> m_WitnessAutomaton;
	
	private final NestedMap3<IPredicate, WitnessNode, Integer, ProductState> m_Cfg2Witness2Result = new NestedMap3<IPredicate, WitnessNode, Integer, WitnessProductAutomaton.ProductState>();
	private final Map<IPredicate, ProductState> m_Result2Product = new HashMap<IPredicate, WitnessProductAutomaton.ProductState>();
	private final IPredicate m_EmptyStackState;
	private final Set<IPredicate> m_InitialStates;
	private final Set<IPredicate> m_FinalStates;
	private final Integer m_StutteringStepsLimit;
	private final WitnessLocationMatcher m_WitnessLocationMatcher;
	private final LinkedHashSet<WitnessAutomatonLetter> m_BadWitnessEdges = new LinkedHashSet<WitnessAutomatonLetter>();
	private final Set<WitnessAutomatonLetter> m_GoodWitnessEdges = new HashSet<WitnessAutomatonLetter>();
	
	private class ProductState {
		private final IPredicate m_CfgAutomatonState;
		private final WitnessNode m_WitnessNode;
		private final Integer m_StutteringSteps;
		private ISLPredicate m_ResultState;

		
		public ProductState(IPredicate cfgAutomatonState,
				WitnessNode witnessAutomatonState,
				Integer stutteringSteps) {
			super();
			m_CfgAutomatonState = cfgAutomatonState;
			m_WitnessNode = witnessAutomatonState;
			m_StutteringSteps = stutteringSteps;
			m_ResultState = constructNewResultState(cfgAutomatonState, witnessAutomatonState, stutteringSteps);
		}
		private ISLPredicate constructNewResultState(IPredicate cfgAutomatonState, WitnessNode witnessNode, Integer stutteringSteps) {
			return m_SmtManager.newTrueSLPredicateWithWitnessNode(((ISLPredicate) cfgAutomatonState).getProgramPoint(), witnessNode, stutteringSteps); 
		}
		
		public IPredicate getCfgAutomatonState() {
			return m_CfgAutomatonState;
		}
		public WitnessNode getWitnessNode() {
			return m_WitnessNode;
		}
		public Integer getStutteringSteps() {
			return m_StutteringSteps;
		}
		public ISLPredicate getResultState() {
			return m_ResultState;
		}
		@Override
		public String toString() {
			return m_ResultState.toString();
		}
	}
	
	public WitnessProductAutomaton(
			IUltimateServiceProvider services,
			INestedWordAutomatonSimple<CodeBlock, IPredicate> controlFlowAutomaton,
			NestedWordAutomaton<WitnessAutomatonLetter, WitnessNode> witnessAutomaton,
			SmtManager smtManager) {
		m_WitnessLocationMatcher = new WitnessLocationMatcher(services, controlFlowAutomaton, witnessAutomaton);
		m_ControlFlowAutomaton = controlFlowAutomaton;
		m_WitnessAutomaton = witnessAutomaton;
		m_SmtManager = smtManager;
		m_InitialStates = constructInitialStates();
		m_FinalStates = new HashSet<IPredicate>();
		m_StutteringStepsLimit = 12;
		m_EmptyStackState = m_ControlFlowAutomaton.getStateFactory().createEmptyStackState();
	}

	private ProductState getOrConstructProductState(
			IPredicate cfgAutomatonState, 
			WitnessNode witnessAutomatonState,
			Integer stutteringSteps) {
		ProductState productState = m_Cfg2Witness2Result.get(cfgAutomatonState, witnessAutomatonState, stutteringSteps);
		if (productState == null) {
			productState = new ProductState(cfgAutomatonState, witnessAutomatonState, stutteringSteps);
			m_Cfg2Witness2Result.put(cfgAutomatonState, witnessAutomatonState, stutteringSteps, productState);
			m_Result2Product.put(productState.getResultState(), productState);
			if (m_ControlFlowAutomaton.isFinal(cfgAutomatonState) && m_WitnessAutomaton.isFinal(witnessAutomatonState)) {
				m_FinalStates.add(productState.getResultState());
			}
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
		return m_ControlFlowAutomaton.getInternalAlphabet();
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
	
	private Set<IPredicate> constructInitialStates() {
		Set<IPredicate> result = new HashSet<IPredicate>();
		for (IPredicate cfg : m_ControlFlowAutomaton.getInitialStates()) {
			for (WitnessNode wa : m_WitnessAutomaton.getInitialStates()) {
				ProductState ps = getOrConstructProductState(cfg, wa, 0);
				result.add(ps.getResultState());
			}
		}
		return result;
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		ArrayList<IPredicate> result = new ArrayList<>();
		for (IPredicate cfg : m_ControlFlowAutomaton.getInitialStates()) {
			for (WitnessNode wa : m_WitnessAutomaton.getInitialStates()) {
				ProductState ps = getOrConstructProductState(cfg, wa, 0);
				result.add(ps.getResultState());
			}
		}
		return result;
	}

	@Override
	public boolean isInitial(IPredicate state) {
		return m_InitialStates.contains(state);
	}

	@Override
	public boolean isFinal(IPredicate state) {
		assert m_Result2Product.keySet().contains(state) : "unknown state";
		return m_FinalStates.contains(state);
	}

	@Override
	public Set<CodeBlock> lettersInternal(IPredicate state) {
		ProductState ps = m_Result2Product.get(state);
		return m_ControlFlowAutomaton.lettersInternal(ps.getCfgAutomatonState());
	}

	@Override
	public Set<CodeBlock> lettersCall(IPredicate state) {
		ProductState ps = m_Result2Product.get(state);
		return m_ControlFlowAutomaton.lettersCall(ps.getCfgAutomatonState());
	}

	@Override
	public Set<CodeBlock> lettersReturn(IPredicate state) {
		ProductState ps = m_Result2Product.get(state);
		return m_ControlFlowAutomaton.lettersReturn(ps.getCfgAutomatonState());
	}

	public Collection<OutgoingInternalTransition<CodeBlock, IPredicate>> constructInternalSuccessors(
			IPredicate state, CodeBlock letter) {
		ProductState ps = m_Result2Product.get(state);
		Collection<OutgoingInternalTransition<CodeBlock, IPredicate>> result = new ArrayList<OutgoingInternalTransition<CodeBlock,IPredicate>>();
		for (OutgoingInternalTransition<CodeBlock, IPredicate> cfgOut : m_ControlFlowAutomaton.internalSuccessors(ps.getCfgAutomatonState(), letter)) {
			Set<IPredicate> succs = computeSuccessorStates(ps, letter, cfgOut.getSucc());
			for (IPredicate succ : succs) {
				result.add(new OutgoingInternalTransition<CodeBlock, IPredicate>(letter, succ));
			}
		}
		return result;
	}
	
	@Override
	public Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state, CodeBlock letter) {
		return constructInternalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<CodeBlock, IPredicate>> internalSuccessors(
			IPredicate state) {
		Collection<OutgoingInternalTransition<CodeBlock, IPredicate>> result = new ArrayList<OutgoingInternalTransition<CodeBlock,IPredicate>>();
		for (CodeBlock cb : this.lettersInternal(state)) {
			result.addAll(constructInternalSuccessors(state, cb));
		}
		return result;
	}
	
	public Collection<OutgoingCallTransition<CodeBlock, IPredicate>> constructCallSuccessors(
			IPredicate state, CodeBlock letter) {
		ProductState ps = m_Result2Product.get(state);
		Collection<OutgoingCallTransition<CodeBlock, IPredicate>> result = new ArrayList<OutgoingCallTransition<CodeBlock,IPredicate>>();
		for (OutgoingCallTransition<CodeBlock, IPredicate> cfgOut : m_ControlFlowAutomaton.callSuccessors(ps.getCfgAutomatonState(), letter)) {
			Set<IPredicate> succs = computeSuccessorStates(ps, letter, cfgOut.getSucc());
			for (IPredicate succ : succs) {
				result.add(new OutgoingCallTransition<CodeBlock, IPredicate>(letter, succ));
			}
		}
		return result;
	}

	@Override
	public Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state, CodeBlock letter) {
		return constructCallSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<CodeBlock, IPredicate>> callSuccessors(
			IPredicate state) {
		Collection<OutgoingCallTransition<CodeBlock, IPredicate>> result = new ArrayList<OutgoingCallTransition<CodeBlock,IPredicate>>();
		for (CodeBlock cb : this.lettersCall(state)) {
			result.addAll(constructCallSuccessors(state, cb));
		}
		return result;
	}

	@Override
	public Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSucccessors(
			IPredicate state, IPredicate hier, CodeBlock letter) {
		return constructReturnSuccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<CodeBlock, IPredicate>> returnSuccessorsGivenHier(
			IPredicate state, IPredicate hier) {
		Collection<OutgoingReturnTransition<CodeBlock, IPredicate>> result = new ArrayList<OutgoingReturnTransition<CodeBlock,IPredicate>>();
		for (CodeBlock cb : this.lettersReturn(state)) {
			result.addAll(constructReturnSuccessors(state, hier, cb));
		}
		return result;
	}
	
	public Collection<OutgoingReturnTransition<CodeBlock, IPredicate>> constructReturnSuccessors(
			IPredicate state, IPredicate hier, CodeBlock letter) {
		ProductState ps = m_Result2Product.get(state);
		ProductState psHier = m_Result2Product.get(hier);
		Collection<OutgoingReturnTransition<CodeBlock, IPredicate>> result = new ArrayList<OutgoingReturnTransition<CodeBlock,IPredicate>>();
		for (OutgoingReturnTransition<CodeBlock, IPredicate> cfgOut : m_ControlFlowAutomaton.returnSucccessors(ps.getCfgAutomatonState(), psHier.getCfgAutomatonState(), letter)) {
			Set<IPredicate> succs = computeSuccessorStates(ps, letter, cfgOut.getSucc());
			for (IPredicate succ : succs) {
				result.add(new OutgoingReturnTransition<CodeBlock, IPredicate>(hier, letter, succ));
			}
		}
		return result;
	}
	
	
	private Set<IPredicate> computeSuccessorStates(ProductState ps, CodeBlock cb, IPredicate cfgSucc) {
		Set<IPredicate> result = new LinkedHashSet<IPredicate>();

		ArrayDeque<WitnessNode> wsSuccStates = new ArrayDeque<WitnessNode>();
		Set<WitnessNode> visited = new HashSet<WitnessNode>();
		wsSuccStates.addAll(skipNonCodeBlockEdges(ps.getWitnessNode()));
		while (!wsSuccStates.isEmpty()) {
			WitnessNode ws = wsSuccStates.removeFirst();
			for (OutgoingInternalTransition<WitnessAutomatonLetter, WitnessNode> out : m_WitnessAutomaton.internalSuccessors(ws)) {
				for (WitnessNode succ : skipNonCodeBlockEdges(out.getSucc())) {
					if (!visited.contains(succ)) {
						visited.add(succ);
						if (isCompatible(cb, out.getLetter())) {
							m_GoodWitnessEdges.add(out.getLetter());
							ProductState succProd = getOrConstructProductState(cfgSucc, succ, 0);
							result.add(succProd.getResultState());
							wsSuccStates.addLast(succ);
						} else {
							m_BadWitnessEdges.add(out.getLetter());
						}
					}
				}
			}
		}
		if (ps.getStutteringSteps() < m_StutteringStepsLimit) {
			ProductState succProd = getOrConstructProductState(cfgSucc, ps.getWitnessNode(), ps.getStutteringSteps() + 1);
			result.add(succProd.getResultState());
		}
		return result;
	}
	
	private Collection<WitnessNode> skipNonCodeBlockEdges(WitnessNode node) {
		Set<WitnessNode> result = new HashSet<WitnessNode>();
		boolean hasOutgoingNodes = false;
		for (OutgoingInternalTransition<WitnessAutomatonLetter, WitnessNode> out : m_WitnessAutomaton.internalSuccessors(node)) {
			hasOutgoingNodes = true;
			if (isCodeBlockEdge(out.getLetter())) {
				result.add(node);
			} else {
				result.addAll(skipNonCodeBlockEdges(out.getSucc()));
			}
		}
		if (!hasOutgoingNodes) {
			result.add(node);
		}
		return result;
	}
	
	private boolean isCodeBlockEdge(WitnessAutomatonLetter edge) {
		return m_WitnessLocationMatcher.isMatchedWitnessEdge(edge);
//		if (edge.isPureAssumptionEdge()) {
//			return true;
//		} else if (edge.isProbalyDeclaration()) {
//			return true;
//		} else {
//			return false;
//		}
	}
	
	
	
	
	public boolean isCompatible(CodeBlock cb, WitnessAutomatonLetter wal) {
		if (cb instanceof Call) {
			Call call = (Call) cb;
			return isCompatible(call, wal);
		} else if (cb instanceof InterproceduralSequentialComposition) {
			InterproceduralSequentialComposition isc = (InterproceduralSequentialComposition) cb;
			return isCompatible(isc, wal);
		} else if (cb instanceof ParallelComposition) {
			ParallelComposition pc = (ParallelComposition) cb;
			return isCompatible(pc, wal);
		} else if (cb instanceof Return) {
			Return ret = (Return) cb;
			return isCompatible(ret, wal);
		} else if (cb instanceof SequentialComposition) {
			SequentialComposition sc = (SequentialComposition) cb;
			return isCompatible(sc, wal);
		} else if (cb instanceof StatementSequence) {
			StatementSequence ss = (StatementSequence) cb;
			return isCompatible(ss, wal);
		} else if (cb instanceof Summary) {
			Summary sum = (Summary) cb;
			return isCompatible(sum.getCallStatement(), wal);
		} else {
			throw new AssertionError("unknown type of CodeBlock");
		}
	}

	
	boolean isCompatible(Call call, WitnessAutomatonLetter wal) {
		return isCompatible(call.getCallStatement(), wal);
	}
	
	boolean isCompatible(InterproceduralSequentialComposition isc, WitnessAutomatonLetter wal) {
		for (CodeBlock cb : isc.getCodeBlocks()) {
			if (isCompatible(cb, wal)) {
				return true;
			}
		}
		return false;
	}
	


	boolean isCompatible(ParallelComposition pc, WitnessAutomatonLetter wal) {
		for (CodeBlock cb : pc.getCodeBlocks()) {
			if (isCompatible(cb, wal)) {
				return true;
			}
		}
		return false;
	}
	
	boolean isCompatible(Return ret, WitnessAutomatonLetter wal) {
		if (isCompatible(ret.getPayload().getLocation(), wal)) {
			return true;
		} else {
			return isCompatible(ret.getCorrespondingCall(), wal);
		}
	}
	
	boolean isCompatible(SequentialComposition sc, WitnessAutomatonLetter wal) {
		for (CodeBlock cb : sc.getCodeBlocks()) {
			if (isCompatible(cb, wal)) {
				return true;
			}
		}
		return false;
	}
	
	boolean isCompatible(StatementSequence ss, WitnessAutomatonLetter wal) {
		for (Statement st : ss.getStatements()) {
			if (isCompatible(st, wal)) {
				return true;
			}
		}
		return false;
	}
	
	boolean isCompatible(Statement st, WitnessAutomatonLetter wal) {
		if (st instanceof AssumeStatement) {
			return isCompatible(((AssumeStatement) st).getFormula().getLocation(), wal);
		} else {
			return isCompatible(st.getLocation(), wal);
		}
	}
	
	

	private boolean isCompatible(ILocation location, WitnessAutomatonLetter wal) {
		return m_WitnessLocationMatcher.isCompatible(location, wal);
	}
	
	public LinkedHashSet<WitnessAutomatonLetter> getBadWitnessEdges() {
		LinkedHashSet<WitnessAutomatonLetter> result = new LinkedHashSet<WitnessAutomatonLetter>(m_BadWitnessEdges);
		result.removeAll(m_GoodWitnessEdges);
		return result;
	}
	
	public String generateBadWitnessInformation() {
		LinkedHashSet<WitnessAutomatonLetter> allBad = getBadWitnessEdges();
		if (allBad.isEmpty()) {
			return "no bad witness edges";
		} else {
			WitnessAutomatonLetter firstBad = allBad.iterator().next();
			Set<ILocation> correspondingLocations = m_WitnessLocationMatcher.getCorrespondingLocations(firstBad);
			StringBuilder sb = new StringBuilder();
			sb.append(allBad.size());
			sb.append(" bad witness edges. ");
			sb.append("First bad witness edge ");
			sb.append(firstBad);
			sb.append(" Corresponding locations: ");
			sb.append(correspondingLocations);
			return sb.toString();
		}
	}


}
