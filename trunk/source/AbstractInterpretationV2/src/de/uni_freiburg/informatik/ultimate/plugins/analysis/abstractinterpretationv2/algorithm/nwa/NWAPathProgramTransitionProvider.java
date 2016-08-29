package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.nwa;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class NWAPathProgramTransitionProvider extends RcfgTransitionProvider
		implements ITransitionProvider<CodeBlock, ProgramPoint>, ILoopDetector<CodeBlock> {

	private final NestedRun<CodeBlock, ?> mCex;
	private final Map<CodeBlock, Integer> mLetter2Index;
	private final CodeBlock mPostErrorLoc;

	public NWAPathProgramTransitionProvider(final NestedRun<CodeBlock, ?> counterexample,
			final IUltimateServiceProvider services, final RootAnnot annotation) {
		super();
		mCex = counterexample;
		mLetter2Index = createLetter2Index(mCex);
		// words count their states, so 0 is first state, length is last state
		mPostErrorLoc = mCex.getSymbol(mCex.getLength() - 2);
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
		return RcfgUtils.getValidCodeBlocks(getSuccessorActions(target), scope);
	}

	@Override
	public boolean isPostErrorLocation(CodeBlock elem, CodeBlock currentScope) {
		assert elem != null;
		return mPostErrorLoc == elem;
	}

	@Override
	public Collection<CodeBlock> filterInitialElements(final Collection<CodeBlock> elems) {
		return super.filterInitialElements(elems).stream().filter(a -> mLetter2Index.containsKey(a))
				.collect(Collectors.toList());
	}

	@Override
	public Collection<CodeBlock> getSuccessorActions(ProgramPoint loc) {
		return loc.getOutgoingEdges().stream().filter(a -> mLetter2Index.containsKey(a) || a instanceof Summary)
				.map(a -> (CodeBlock) a).collect(Collectors.toList());
	}

	@Override
	public boolean isEnteringLoop(CodeBlock transition) {
		assert transition != null;
		return null != LoopEntryAnnotation.getAnnotation(transition);
	}
}
