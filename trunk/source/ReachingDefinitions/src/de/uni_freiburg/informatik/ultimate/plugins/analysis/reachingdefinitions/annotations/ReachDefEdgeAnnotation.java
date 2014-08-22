package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

public class ReachDefEdgeAnnotation extends ReachDefBaseAnnotation {

	private static final long serialVersionUID = 1L;

	private RCFGEdge mEdge;
	private DefCollector mDefCollector;
	private UseCollector mUseCollector;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mProvider;

	public ReachDefEdgeAnnotation(RCFGEdge e, IAnnotationProvider<ReachDefStatementAnnotation> provider) {
		mEdge = e;
		mProvider = provider;
	}

	@Override
	protected HashMap<ScopedBoogieVar, HashSet<Statement>> getDefs() {
		if (mEdge == null) {
			return new HashMap<>();
		}

		if (mDefCollector == null) {
			mDefCollector = new DefCollector(mProvider);
		}

		return mDefCollector.collect(mEdge);
	}

	@Override
	protected HashMap<ScopedBoogieVar, HashSet<Statement>> getUse() {
		if (mEdge == null) {
			return new HashMap<>();
		}
		if (mUseCollector == null) {
			mUseCollector = new UseCollector(mProvider);
		}

		return mUseCollector.collect(mEdge);
	}
}
