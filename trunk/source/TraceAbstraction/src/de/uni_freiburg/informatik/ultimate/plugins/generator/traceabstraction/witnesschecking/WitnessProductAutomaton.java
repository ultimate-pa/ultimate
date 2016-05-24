/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNodeAnnotation;

public class WitnessProductAutomaton implements INestedWordAutomatonSimple<CodeBlock, IPredicate> {
	private final SmtManager mSmtManager;
	private final INestedWordAutomatonSimple<CodeBlock, IPredicate> mControlFlowAutomaton;
	private final INestedWordAutomatonSimple<WitnessEdge, WitnessNode> mWitnessAutomaton;
	
	private final NestedMap3<IPredicate, WitnessNode, Integer, ProductState> mCfg2Witness2Result = new NestedMap3<IPredicate, WitnessNode, Integer, WitnessProductAutomaton.ProductState>();
	private final Map<IPredicate, ProductState> mResult2Product = new HashMap<IPredicate, WitnessProductAutomaton.ProductState>();
	private final IPredicate mEmptyStackState;
	private final Set<IPredicate> mInitialStates;
	private final Set<IPredicate> mFinalStates;
	private final Integer mStutteringStepsLimit = 10;
	private final WitnessLocationMatcher mWitnessLocationMatcher;
	private final LinkedHashSet<WitnessEdge> mBadWitnessEdges = new LinkedHashSet<WitnessEdge>();
	private final Set<WitnessEdge> mGoodWitnessEdges = new HashSet<WitnessEdge>();
	
	private class ProductState {
		private final IPredicate mCfgAutomatonState;
		private final WitnessNode mWitnessNode;
		private final Integer mStutteringSteps;
		private ISLPredicate mResultState;

		
		public ProductState(IPredicate cfgAutomatonState,
				WitnessNode witnessAutomatonState,
				Integer stutteringSteps) {
			super();
			mCfgAutomatonState = cfgAutomatonState;
			mWitnessNode = witnessAutomatonState;
			mStutteringSteps = stutteringSteps;
			mResultState = constructNewResultState(cfgAutomatonState, witnessAutomatonState, stutteringSteps);
		}
		private ISLPredicate constructNewResultState(IPredicate cfgAutomatonState, WitnessNode witnessNode, Integer stutteringSteps) {
			return mSmtManager.getPredicateFactory().newTrueSLPredicateWithWitnessNode(
					((ISLPredicate) cfgAutomatonState).getProgramPoint(), witnessNode, stutteringSteps); 
		}
		
		public IPredicate getCfgAutomatonState() {
			return mCfgAutomatonState;
		}
		public WitnessNode getWitnessNode() {
			return mWitnessNode;
		}
		public Integer getStutteringSteps() {
			return mStutteringSteps;
		}
		public ISLPredicate getResultState() {
			return mResultState;
		}
		@Override
		public String toString() {
			return mResultState.toString();
		}
	}
	
	public WitnessProductAutomaton(
			IUltimateServiceProvider services,
			INestedWordAutomatonSimple<CodeBlock, IPredicate> controlFlowAutomaton,
			NestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton,
			SmtManager smtManager) {
		mWitnessLocationMatcher = new WitnessLocationMatcher(services, controlFlowAutomaton, witnessAutomaton);
		mControlFlowAutomaton = controlFlowAutomaton;
		mWitnessAutomaton = witnessAutomaton;
		mSmtManager = smtManager;
		mInitialStates = constructInitialStates();
		mFinalStates = new HashSet<IPredicate>();
		mEmptyStackState = mControlFlowAutomaton.getStateFactory().createEmptyStackState();
	}

	private ProductState getOrConstructProductState(
			IPredicate cfgAutomatonState, 
			WitnessNode witnessAutomatonState,
			Integer stutteringSteps) {
		ProductState productState = mCfg2Witness2Result.get(cfgAutomatonState, witnessAutomatonState, stutteringSteps);
		if (productState == null) {
			productState = new ProductState(cfgAutomatonState, witnessAutomatonState, stutteringSteps);
			mCfg2Witness2Result.put(cfgAutomatonState, witnessAutomatonState, stutteringSteps, productState);
			mResult2Product.put(productState.getResultState(), productState);
			if (mControlFlowAutomaton.isFinal(cfgAutomatonState) && mWitnessAutomaton.isFinal(witnessAutomatonState)) {
				mFinalStates.add(productState.getResultState());
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
		return mControlFlowAutomaton.getInternalAlphabet();
	}

	@Override
	public Set<CodeBlock> getCallAlphabet() {
		return mControlFlowAutomaton.getCallAlphabet();
	}

	@Override
	public Set<CodeBlock> getReturnAlphabet() {
		return mControlFlowAutomaton.getReturnAlphabet();
	}

	@Override
	public StateFactory<IPredicate> getStateFactory() {
		return mControlFlowAutomaton.getStateFactory();
	}

	@Override
	public IPredicate getEmptyStackState() {
		return mEmptyStackState;
	}
	
	private Set<IPredicate> constructInitialStates() {
		Set<IPredicate> result = new HashSet<IPredicate>();
		for (IPredicate cfg : mControlFlowAutomaton.getInitialStates()) {
			for (WitnessNode wa : mWitnessAutomaton.getInitialStates()) {
				ProductState ps = getOrConstructProductState(cfg, wa, 0);
				result.add(ps.getResultState());
			}
		}
		return result;
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		ArrayList<IPredicate> result = new ArrayList<>();
		for (IPredicate cfg : mControlFlowAutomaton.getInitialStates()) {
			for (WitnessNode wa : mWitnessAutomaton.getInitialStates()) {
				ProductState ps = getOrConstructProductState(cfg, wa, 0);
				result.add(ps.getResultState());
			}
		}
		return result;
	}

	@Override
	public boolean isInitial(IPredicate state) {
		return mInitialStates.contains(state);
	}

	@Override
	public boolean isFinal(IPredicate state) {
		assert mResult2Product.keySet().contains(state) : "unknown state";
		return mFinalStates.contains(state);
	}

	@Override
	public Set<CodeBlock> lettersInternal(IPredicate state) {
		ProductState ps = mResult2Product.get(state);
		return mControlFlowAutomaton.lettersInternal(ps.getCfgAutomatonState());
	}

	@Override
	public Set<CodeBlock> lettersCall(IPredicate state) {
		ProductState ps = mResult2Product.get(state);
		return mControlFlowAutomaton.lettersCall(ps.getCfgAutomatonState());
	}

	@Override
	public Set<CodeBlock> lettersReturn(IPredicate state) {
		ProductState ps = mResult2Product.get(state);
		return mControlFlowAutomaton.lettersReturn(ps.getCfgAutomatonState());
	}

	public Collection<OutgoingInternalTransition<CodeBlock, IPredicate>> constructInternalSuccessors(
			IPredicate state, CodeBlock letter) {
		ProductState ps = mResult2Product.get(state);
		Collection<OutgoingInternalTransition<CodeBlock, IPredicate>> result = new ArrayList<OutgoingInternalTransition<CodeBlock,IPredicate>>();
		for (OutgoingInternalTransition<CodeBlock, IPredicate> cfgOut : mControlFlowAutomaton.internalSuccessors(ps.getCfgAutomatonState(), letter)) {
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
		ProductState ps = mResult2Product.get(state);
		Collection<OutgoingCallTransition<CodeBlock, IPredicate>> result = new ArrayList<OutgoingCallTransition<CodeBlock,IPredicate>>();
		for (OutgoingCallTransition<CodeBlock, IPredicate> cfgOut : mControlFlowAutomaton.callSuccessors(ps.getCfgAutomatonState(), letter)) {
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
		ProductState ps = mResult2Product.get(state);
		ProductState psHier = mResult2Product.get(hier);
		Collection<OutgoingReturnTransition<CodeBlock, IPredicate>> result = new ArrayList<OutgoingReturnTransition<CodeBlock,IPredicate>>();
		for (OutgoingReturnTransition<CodeBlock, IPredicate> cfgOut : mControlFlowAutomaton.returnSucccessors(ps.getCfgAutomatonState(), psHier.getCfgAutomatonState(), letter)) {
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
			for (OutgoingInternalTransition<WitnessEdge, WitnessNode> out : mWitnessAutomaton.internalSuccessors(ws)) {
				for (WitnessNode succ : skipNonCodeBlockEdges(out.getSucc())) {
					if (!visited.contains(succ)) {
						visited.add(succ);
						if (isSink(out.getSucc())) {
							// successor is sink, do nothing
						} else {
							if (isCompatible(cb, out.getLetter())) {
								mGoodWitnessEdges.add(out.getLetter());
								ProductState succProd = getOrConstructProductState(cfgSucc, succ, 0);
								result.add(succProd.getResultState());
								wsSuccStates.addLast(succ);
							} else {
								mBadWitnessEdges.add(out.getLetter());
							}
						}
					}
				}
			}
		}
		if (ps.getStutteringSteps() < mStutteringStepsLimit) {
			final int stutteringStepsCounter;
			if (isStateOfInitFunction(ps.mCfgAutomatonState)) {
				stutteringStepsCounter = ps.getStutteringSteps();
			} else {
				stutteringStepsCounter = ps.getStutteringSteps() + 1;
			}
			ProductState succProd = getOrConstructProductState(cfgSucc, ps.getWitnessNode(), stutteringStepsCounter);
			result.add(succProd.getResultState());
		}
		return result;
	}
	
	private boolean isStateOfInitFunction(IPredicate cfgAutomatonState) {
		ProgramPoint pp = ((SPredicate) cfgAutomatonState).getProgramPoint();
		String proc = pp.getProcedure();
		if (proc.equals("ULTIMATE.init")) {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Nodes can be marked as sink.
	 */
	private boolean isSink(WitnessNode succ) {
		WitnessNodeAnnotation wan = WitnessNodeAnnotation.getAnnotation(succ);
		if (wan == null) {
			return false;
		} else {
			return wan.isSink();
		}
	}

	private Collection<WitnessNode> skipNonCodeBlockEdges(WitnessNode node) {
		Set<WitnessNode> result = new HashSet<WitnessNode>();
		boolean hasOutgoingNodes = false;
		for (OutgoingInternalTransition<WitnessEdge, WitnessNode> out : mWitnessAutomaton.internalSuccessors(node)) {
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
	
	private boolean isCodeBlockEdge(WitnessEdge edge) {
		return mWitnessLocationMatcher.isMatchedWitnessEdge(edge);
//		if (edge.isPureAssumptionEdge()) {
//			return true;
//		} else if (edge.isProbalyDeclaration()) {
//			return true;
//		} else {
//			return false;
//		}
	}
	
	
	
	
	public boolean isCompatible(CodeBlock cb, WitnessEdge we) {
		if (cb instanceof Call) {
			Call call = (Call) cb;
			return isCompatible(call, we);
		} else if (cb instanceof InterproceduralSequentialComposition) {
			InterproceduralSequentialComposition isc = (InterproceduralSequentialComposition) cb;
			return isCompatible(isc, we);
		} else if (cb instanceof ParallelComposition) {
			ParallelComposition pc = (ParallelComposition) cb;
			return isCompatible(pc, we);
		} else if (cb instanceof Return) {
			Return ret = (Return) cb;
			return isCompatible(ret, we);
		} else if (cb instanceof SequentialComposition) {
			SequentialComposition sc = (SequentialComposition) cb;
			return isCompatible(sc, we);
		} else if (cb instanceof StatementSequence) {
			StatementSequence ss = (StatementSequence) cb;
			return isCompatible(ss, we);
		} else if (cb instanceof Summary) {
			Summary sum = (Summary) cb;
			return isCompatible(sum.getCallStatement(), we);
		} else {
			throw new AssertionError("unknown type of CodeBlock");
		}
	}

	
	boolean isCompatible(Call call, WitnessEdge we) {
		return isCompatible(call.getCallStatement(), we);
	}
	
	boolean isCompatible(InterproceduralSequentialComposition isc, WitnessEdge we) {
		for (CodeBlock cb : isc.getCodeBlocks()) {
			if (isCompatible(cb, we)) {
				return true;
			}
		}
		return false;
	}
	


	boolean isCompatible(ParallelComposition pc, WitnessEdge we) {
		for (CodeBlock cb : pc.getCodeBlocks()) {
			if (isCompatible(cb, we)) {
				return true;
			}
		}
		return false;
	}
	
	boolean isCompatible(Return ret, WitnessEdge we) {
		if (isCompatible(ret.getPayload().getLocation(), we)) {
			return true;
		} else {
			return isCompatible(ret.getCorrespondingCall(), we);
		}
	}
	
	boolean isCompatible(SequentialComposition sc, WitnessEdge we) {
		for (CodeBlock cb : sc.getCodeBlocks()) {
			if (isCompatible(cb, we)) {
				return true;
			}
		}
		return false;
	}
	
	boolean isCompatible(StatementSequence ss, WitnessEdge we) {
		for (Statement st : ss.getStatements()) {
			if (isCompatible(st, we)) {
				return true;
			}
		}
		return false;
	}
	
	boolean isCompatible(Statement st, WitnessEdge we) {
		if (st instanceof AssumeStatement) {
			return isCompatible(((AssumeStatement) st).getFormula().getLocation(), we);
		} else {
			return isCompatible(st.getLocation(), we);
		}
	}
	
	

	private boolean isCompatible(ILocation location, WitnessEdge we) {
		return mWitnessLocationMatcher.isCompatible(location, we);
	}
	
	private LinkedHashSet<WitnessEdge> getBadWitnessEdges() {
		LinkedHashSet<WitnessEdge> result = new LinkedHashSet<WitnessEdge>(mBadWitnessEdges);
		result.removeAll(mGoodWitnessEdges);
		return result;
	}
	
	public String generateBadWitnessInformation() {
		LinkedHashSet<WitnessEdge> allBad = getBadWitnessEdges();
		if (allBad.isEmpty()) {
			return "no bad witness edges";
		} else {
			WitnessEdge firstBad = allBad.iterator().next();
			Set<ILocation> correspondingLocations = mWitnessLocationMatcher.getCorrespondingLocations(firstBad);
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
