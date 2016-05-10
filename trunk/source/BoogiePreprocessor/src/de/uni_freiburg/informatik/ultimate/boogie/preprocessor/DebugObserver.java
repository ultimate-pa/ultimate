/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.BaseObserver;
import de.uni_freiburg.informatik.ultimate.models.IElement;
import de.uni_freiburg.informatik.ultimate.models.IPayload;
import de.uni_freiburg.informatik.ultimate.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.models.structure.IWalkable;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

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
				Map<String, IAnnotations> annot = payload.getAnnotations();
				Collection<IAnnotations> annots = CoreUtil.flattenMapValuesToCollection(annot);
				checkAnnotations(node, annots);
			}
		}
	}

	private void checkAnnotations(IWalkable node, Collection<IAnnotations> annots) {
		for (IAnnotations annot : annots) {
			if (annot instanceof Overapprox)
				mLogger.info("Overapprox found");
		}
	}

}
