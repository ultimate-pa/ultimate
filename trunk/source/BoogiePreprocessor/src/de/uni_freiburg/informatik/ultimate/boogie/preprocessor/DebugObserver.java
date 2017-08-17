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

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.lib.observers.BaseObserver;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class DebugObserver extends BaseObserver {

	private final ILogger mLogger;

	public DebugObserver(final ILogger logger) {
		mLogger = logger;
	}

	@Override
	public boolean process(final IElement root) throws Throwable {
		if (root instanceof IWalkable) {
			walkTree((IWalkable) root);
		}
		return false;
	}

	private void walkTree(final IWalkable root) {
		final Queue<IWalkable> queue = new LinkedList<>();
		final HashSet<IWalkable> processed = new HashSet<>();
		queue.add(root);
		while (!queue.isEmpty()) {
			final IWalkable node = queue.poll();
			if (!processed.add(node)) {
				mLogger.debug("This is not a tree! " + node + " is on a cylce");
				continue;
			}
			checkNode(node);

			for (final IWalkable succ : node.getSuccessors()) {
				if (succ == null) {
					mLogger.debug(node + " contains null successors");
					continue;
				}
				queue.add(succ);
			}
		}
	}

	private void checkNode(final IWalkable node) {
		if (node.hasPayload()) {
			final IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				final Map<String, IAnnotations> annot = payload.getAnnotations();
				final Collection<IAnnotations> annots = CoreUtil.flattenMapValuesToCollection(annot);
				checkAnnotations(node, annots);
			}
		}
	}

	private void checkAnnotations(final IWalkable node, final Collection<IAnnotations> annots) {
		for (final IAnnotations annot : annots) {
			if (annot instanceof Overapprox) {
				mLogger.info("Overapprox found");
			}
		}
	}

}
