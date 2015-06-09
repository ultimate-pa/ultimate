package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizeproduct;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;

public abstract class BaseProductOptimizer {
	protected final IUltimateServiceProvider mServices;
	protected final Logger mLogger;

	protected final RootNode mResult;
	protected int mRemovedEdges;
	protected int mRemovedLocations;
	protected final CodeBlockFactory mCbf;

	public BaseProductOptimizer(RootNode product, IUltimateServiceProvider services, IToolchainStorage storage) {
		assert services != null;
		assert product != null;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCbf = (CodeBlockFactory) storage.getStorable(CodeBlockFactory.s_CodeBlockFactoryKeyInToolchainStorage);
		mRemovedEdges = 0;
		mRemovedLocations = 0;
		init(product, services);
		mResult = process(product);
	}

	protected void init(RootNode root, IUltimateServiceProvider services) {

	}

	protected abstract RootNode process(RootNode root);

	public abstract boolean isGraphChanged();

	protected List<ProgramPoint> getSuccessors(ProgramPoint point) {
		final List<ProgramPoint> rtr = new ArrayList<>();
		for (final RCFGEdge edge : point.getOutgoingEdges()) {
			rtr.add((ProgramPoint) edge.getTarget());
		}
		return rtr;
	}

	protected void removeDisconnectedLocations(RootNode root) {
		final Deque<ProgramPoint> toRemove = new ArrayDeque<>();

		for (final Entry<String, Map<String, ProgramPoint>> procPair : root.getRootAnnot().getProgramPoints()
				.entrySet()) {
			for (final Entry<String, ProgramPoint> pointPair : procPair.getValue().entrySet()) {
				if (pointPair.getValue().getIncomingEdges().size() == 0) {
					toRemove.add(pointPair.getValue());
				}
			}
		}

		while (!toRemove.isEmpty()) {
			final ProgramPoint current = toRemove.removeFirst();
			final List<RCFGEdge> outEdges = new ArrayList<>(current.getOutgoingEdges());
			for (final RCFGEdge out : outEdges) {
				final ProgramPoint target = (ProgramPoint) out.getTarget();
				if (target.getIncomingEdges().size() == 1) {
					toRemove.addLast(target);
				}
				out.disconnectSource();
				out.disconnectTarget();
				mRemovedEdges++;
			}
			removeDisconnectedLocation(root, current);
		}
	}

	protected void removeDisconnectedLocation(RootNode root, ProgramPoint toRemove) {
		// TODO: remove stuff from the root annotation
		final RootAnnot rootAnnot = root.getRootAnnot();
		final String procName = toRemove.getProcedure();
		final String locName = toRemove.getPosition();
		final ProgramPoint removed = rootAnnot.getProgramPoints().get(procName).remove(locName);
		assert removed == toRemove;
		mRemovedLocations++;
	}

	public RootNode getResult() {
		return mResult;
	}

	protected void generateTransFormula(RootNode root, StatementSequence ss) {
		final Boogie2SMT b2smt = root.getRootAnnot().getBoogie2SMT();
		final TransFormulaBuilder tfb = new TransFormulaBuilder(b2smt, mServices);
		tfb.addTransitionFormulas((CodeBlock) ss, ((ProgramPoint) ss.getSource()).getProcedure());
		assert ss.getTransitionFormula() != null;
	}
}