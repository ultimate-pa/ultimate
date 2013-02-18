package de.uni_freiburg.informatik.ultimate.irs.dependencies.observers;

import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.visitors.SequencingVisitor;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.visitors.UseDefVisitor;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.walker.ObserverDispatcher;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.walker.RCFGWalkerUnroller;
import de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.walker.ObserverDispatcherSequential;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;

/**
 * 
 * @author dietsch
 * 
 */
public class DependencyFinder extends BaseObserver {

	private final int mUnrollings;

	public DependencyFinder() {
		super();
		mUnrollings = 1;
	}

	@Override
	public boolean process(IElement root) {

		doit(root, mUnrollings);

		// for (int i = 1; i <= 3; ++i) {
		// doit(root, i);
		// }

		return false;
	}

	private void doit(IElement root, int unrollings) {
		ObserverDispatcher od = new ObserverDispatcherSequential();
		RCFGWalkerUnroller walker = new RCFGWalkerUnroller(od, unrollings);
		od.setWalker(walker);

		//walker.addObserver(new DebugRCFGVisitor(500));
		walker.addObserver(new UseDefVisitor());
		walker.addObserver(new SequencingVisitor(walker));
		walker.run((RCFGNode) root);

		DebugFileWriterDietsch dfw = new DebugFileWriterDietsch(
				walker.getPaths(), unrollings);
		dfw.run();
	}

}
