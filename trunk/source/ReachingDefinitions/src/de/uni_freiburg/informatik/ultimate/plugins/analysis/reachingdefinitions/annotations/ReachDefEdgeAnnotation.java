package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie.ScopedBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

public class ReachDefEdgeAnnotation extends ReachDefBaseAnnotation {

	private static final long serialVersionUID = 1L;

	private RCFGEdge mEdge;
	private DefCollector mDefCollector;
	private UseCollector mUseCollector;
	private final IAnnotationProvider<ReachDefStatementAnnotation> mProvider;
	private final String mKey;

	public ReachDefEdgeAnnotation(RCFGEdge e, IAnnotationProvider<ReachDefStatementAnnotation> provider, String key) {
		mEdge = e;
		mProvider = provider;
		mKey = key;
	}

	public ReachDefEdgeAnnotation(RCFGEdge e, IAnnotationProvider<ReachDefStatementAnnotation> provider) {
		this(e, provider, null);
	}

	public String getKey() {
		return mKey;
	}

	@Override
	public HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> getDefs() {
		if (mEdge == null) {
			return new HashMap<>();
		}

		if (mDefCollector == null) {
			mDefCollector = new DefCollector(mProvider, mKey);
		}

		return mDefCollector.collect(mEdge);
	}

	@Override
	public HashMap<ScopedBoogieVar, HashSet<IndexedStatement>> getUse() {
		if (mEdge == null) {
			return new HashMap<>();
		}
		if (mUseCollector == null) {
			mUseCollector = new UseCollector(mProvider, mKey);
		}

		return mUseCollector.collect(mEdge);
	}
}
