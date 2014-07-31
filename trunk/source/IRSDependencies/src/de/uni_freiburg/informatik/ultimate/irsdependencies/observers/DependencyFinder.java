package de.uni_freiburg.informatik.ultimate.irsdependencies.observers;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.DebugRCFGVisitor;
import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors.DummyVisitor;
import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker.ObserverDispatcher;
import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker.ObserverDispatcherSequential;
import de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.walker.RCFGWalkerUnroller;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * 
 * @author dietsch
 * 
 */
public class DependencyFinder extends BaseObserver {

	private final int mUnrollings;
	private final Logger mLogger;

	public DependencyFinder(Logger logger) {
		super();
		mUnrollings = 1;
		mLogger = logger;
	}

	@Override
	public boolean process(IElement root) {

		// doit(root, mUnrollings);


		// for (int i = 1; i <= 3; ++i) {
		// doit(root, i);
		// }

		return false;
	}

	private void doit(IElement root, int unrollings) {
		ObserverDispatcher od = new ObserverDispatcherSequential(mLogger);
		RCFGWalkerUnroller walker = new RCFGWalkerUnroller(od, mLogger, unrollings);
		od.setWalker(walker);

		walker.addObserver(new DebugRCFGVisitor(mLogger, 500));
		// walker.addObserver(new UseDefVisitor());
		// walker.addObserver(new SequencingVisitor(walker));
		walker.run((RCFGNode) root);

		DebugFileWriterDietsch dfw = new DebugFileWriterDietsch(walker.getPaths(), mLogger, unrollings);
		dfw.run();
	}



}
