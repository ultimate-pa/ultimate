package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.nwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.annotation.LoopEntryAnnotation;
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
public class NWAPathProgramTransitionProvider
		implements ITransitionProvider<CodeBlock, ProgramPoint>, ILoopDetector<CodeBlock> {

	private final NestedRun<CodeBlock, ?> mCex;
	private Map<CodeBlock, Integer> mLetter2Index;
	private CodeBlock mPostErrorLoc;
	// private final Set<ProgramPoint> mLoopLocations;

	public NWAPathProgramTransitionProvider(final NestedRun<CodeBlock, ?> counterexample,
			final IUltimateServiceProvider services, final RootAnnot annotation) {
		mCex = counterexample;
		mLetter2Index = createLetter2Index(mCex);
		// words count their states, so 0 is first state, length is last state
		mPostErrorLoc = mCex.getSymbol(mCex.getLength() - 2);
		// mLoopLocations = annotations.getLoopLocations().keySet();
	}

	private Map<CodeBlock, Integer> createLetter2Index(final NestedRun<CodeBlock, ?> cex) {
		final Map<CodeBlock, Integer> rtr = new HashMap<>();
		final int length = cex.getLength();
		for (int i = 0; i < length - 1; ++i) {
			rtr.put(cex.getSymbol(i), i);
		}
		return rtr;
	}

	@Override
	public Collection<CodeBlock> getSuccessors(CodeBlock elem, CodeBlock scope) {
		final ProgramPoint target = getTarget(elem);
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
	public ProgramPoint getSource(CodeBlock current) {
		return (ProgramPoint) current.getSource();
	}

	@Override
	public ProgramPoint getTarget(CodeBlock current) {
		return (ProgramPoint) current.getTarget();
	}

	@Override
	public Collection<CodeBlock> getSuccessorActions(ProgramPoint loc) {
		return loc.getOutgoingEdges().stream().filter(a -> mLetter2Index.containsKey(a)).map(a -> (CodeBlock) a)
				.collect(Collectors.toList());
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
		final LoopEntryAnnotation leannot = LoopEntryAnnotation.getAnnotation(transition);
		return leannot != null;
	}
}
