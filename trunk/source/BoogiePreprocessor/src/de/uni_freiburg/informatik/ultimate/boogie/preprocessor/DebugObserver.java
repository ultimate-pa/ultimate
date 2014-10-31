package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;

public class DebugObserver extends BaseObserver {

	private final Logger mLogger;

	public DebugObserver(Logger logger) {
		mLogger = logger;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (root instanceof IWalkable) {
			walkTree((IWalkable) root);
		}
		return false;
	}

	private void walkTree(IWalkable root) {
		Queue<IWalkable> queue = new LinkedList<>();
		HashSet<IWalkable> processed = new HashSet<>();
		queue.add(root);
		while (!queue.isEmpty()) {
			IWalkable node = queue.poll();
			if (!processed.add(node)) {
				mLogger.debug("This is not a tree! " + node + " is on a cylce");
				continue;
			}
			checkNode(node);

			for (IWalkable succ : node.getSuccessors()) {
				if (succ == null) {
					mLogger.debug(node + " contains null successors");
					continue;
				}
				queue.add(succ);
			}

		}
	}

	private void checkNode(IWalkable node) {
		if (node.hasPayload()) {
			IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				HashMap<String, IAnnotations> annot = payload.getAnnotations();
				Collection<IAnnotations> annots = CoreUtil.flattenMapValuesToCollection(annot);
				checkAnnotations(node, annots);
			}
		}

	}

	private void checkAnnotations(IWalkable node, Collection<IAnnotations> annots) {
		if (annots instanceof Overapprox) {
			mLogger.info("Overapprox found");
		}
	}

}
