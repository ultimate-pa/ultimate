package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.nwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class NWAPathProgramTransitionProvider<LOCATION>
		implements ITransitionProvider<CodeBlock, LOCATION>, ILoopDetector<CodeBlock> {

	private final INestedWordAutomatonOldApi<CodeBlock, LOCATION> mAutomata;
	private final NestedRun<CodeBlock, LOCATION> mCex;
	private Map<CodeBlock, Integer> mLetter2Index;
	private CodeBlock mPostErrorLoc;
	private final Set<ProgramPoint> mLoopLocations;

	public NWAPathProgramTransitionProvider(final INestedWordAutomatonOldApi<CodeBlock, LOCATION> currentAutomata,
			final NestedRun<CodeBlock, LOCATION> counterexample, final IUltimateServiceProvider services,
			final RootAnnot annotation) {
		mAutomata = currentAutomata;
		mCex = counterexample;
		mLetter2Index = createLetter2Index(mCex);
		// words count their states, so 0 is first state, length is last state
		mPostErrorLoc = mCex.getSymbol(mCex.getLength() - 2);
		mLoopLocations = annotation.getLoopLocations().keySet();
	}

	private Map<CodeBlock, Integer> createLetter2Index(final NestedRun<CodeBlock, LOCATION> cex) {
		final Map<CodeBlock, Integer> rtr = new HashMap<>();
		final int length = cex.getLength();
		for (int i = 0; i < length - 1; ++i) {
			rtr.put(cex.getSymbol(i), i);
		}
		return rtr;
	}

	@Override
	public Collection<CodeBlock> getSuccessors(CodeBlock elem, CodeBlock scope) {
		final LOCATION target = getTarget(elem);
		if (target == null) {
			return Collections.emptyList();
		}
		final Collection<CodeBlock> successors = getSuccessorActions(target);
		final Collection<CodeBlock> rtr = getValidCodeBlocks(successors, scope);
		return rtr;
	}

	@Override
	public boolean isPostErrorLocation(CodeBlock elem, CodeBlock currentScope) {
		assert elem != null;
		return mPostErrorLoc == elem;
	}

	@Override
	public String toLogString(CodeBlock elem) {
		return elem.toString();
	}

	@Override
	public Collection<CodeBlock> filterInitialElements(Collection<CodeBlock> elems) {
		if (elems == null) {
			return Collections.emptyList();
		}
		final List<CodeBlock> rtr = new ArrayList<>(elems.size());
		for (final CodeBlock elem : elems) {
			if (!isUnnecessarySummary(elem)) {
				rtr.add(elem);
			}
		}
		return rtr;
	}

	@Override
	public boolean isEnteringScope(CodeBlock current) {
		if (current instanceof Call) {
			return true;
		}
		return false;
	}

	@Override
	public boolean isLeavingScope(CodeBlock current, CodeBlock scope) {
		assert current != null;
		return isCorrespondingCall(current, scope);
	}

	@Override
	public LOCATION getSource(CodeBlock current) {
		final Integer index = mLetter2Index.get(current);
		if (index == null) {
			// this is not part of the CEX, it must be part of the path program
			// TODO: Implement
			throw new UnsupportedOperationException();
		} else {
			final LOCATION locAtIndex = mCex.getStateAtPosition(index);
			return locAtIndex;
		}
	}

	@Override
	public LOCATION getTarget(CodeBlock current) {
		final Integer index = mLetter2Index.get(current);
		if (index == null) {
			// this is not part of the CEX, it must be part of the path program
			// TODO: Implement
			throw new UnsupportedOperationException();
		} else {
			final LOCATION locAtIndex = mCex.getStateAtPosition(index + 1);
			return locAtIndex;
		}
	}

	@Override
	public Collection<CodeBlock> getSuccessorActions(LOCATION loc) {
		final Collection<CodeBlock> rtr = new ArrayList<>();
		for (OutgoingInternalTransition<CodeBlock, LOCATION> internalSucc : mAutomata.internalSuccessors(loc)) {
			final CodeBlock succ = internalSucc.getLetter();
			if (mLetter2Index.containsKey(succ)) {
				rtr.add(succ);
			}
		}
		for (OutgoingCallTransition<CodeBlock, LOCATION> callSucc : mAutomata.callSuccessors(loc)) {
			final CodeBlock succ = callSucc.getLetter();
			if (mLetter2Index.containsKey(succ)) {
				rtr.add(succ);
			}
		}
		for (OutgoingReturnTransition<CodeBlock, LOCATION> returnSucc : mAutomata.returnSuccessors(loc)) {
			final CodeBlock succ = returnSucc.getLetter();
			if (mLetter2Index.containsKey(succ)) {
				rtr.add(succ);
			}
		}
		// TODO: Add loop successors
		return rtr;
	}

	private Collection<CodeBlock> getValidCodeBlocks(final Collection<CodeBlock> successors, CodeBlock scope) {
		if (successors == null) {
			return Collections.emptyList();
		}
		final List<CodeBlock> rtr = new ArrayList<>(successors.size());
		for (final RCFGEdge successor : successors) {
			final CodeBlock cbSucc = getValidCodeBlock(successor, scope);
			if (cbSucc == null) {
				continue;
			}
			rtr.add(cbSucc);
		}
		return rtr;
	}

	private CodeBlock getValidCodeBlock(final RCFGEdge successor, CodeBlock scope) {
		if (!(successor instanceof CodeBlock)) {
			return null;
		}
		if (isUnnecessarySummary(successor)) {
			return null;
		}

		final CodeBlock cbSucc = (CodeBlock) successor;
		if (cbSucc instanceof Return) {
			if (!isCorrespondingCall(cbSucc, scope)) {
				return null;
			}
		}
		return (CodeBlock) successor;
	}

	private boolean isUnnecessarySummary(RCFGEdge edge) {
		if (edge instanceof Summary) {
			Summary sum = (Summary) edge;
			return sum.calledProcedureHasImplementation();
		}
		return false;
	}

	private boolean isCorrespondingCall(CodeBlock current, CodeBlock currentScope) {
		if (currentScope == null) {
			return false;
		}
		if (current instanceof Return) {
			Return currReturn = (Return) current;
			assert currentScope instanceof Call;
			return currReturn.getCorrespondingCall().equals(currentScope);
		}
		return false;
	}

	@Override
	public boolean isEnteringLoop(CodeBlock transition) {
		assert transition != null;
		final LOCATION source = getSource(transition);
		return mLoopLocations.contains(source);
	}
}
