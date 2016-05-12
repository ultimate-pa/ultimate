/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CFGConsoleOut plug-in.
 * 
 * The ULTIMATE CFGConsoleOut plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CFGConsoleOut plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CFGConsoleOut plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CFGConsoleOut plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CFGConsoleOut plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.output.cfgconsoleout;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.models.IElement;
import de.uni_freiburg.informatik.ultimate.models.IPayload;
import de.uni_freiburg.informatik.ultimate.models.ModelType;
import de.uni_freiburg.informatik.ultimate.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.models.structure.IWalkable;

public class CFGConsoleOutObserver implements IUnmanagedObserver {

	private Map<IElement, String> mSeenList;
	private int mNumRoots;
	private ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final PrintWriter mWriter;

	public CFGConsoleOutObserver(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mWriter = new PrintWriter(System.out);
	}

	@Override
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) throws Throwable {
		mSeenList = new HashMap<IElement, String>();
		mNumRoots = -1;
	}

	@Override
	public boolean process(IElement root) {
		if (root instanceof IWalkable) {
			dfstraverse((IWalkable) root, "" + (++mNumRoots));
		}
		return false;
	}

	@Override
	public void finish() {
	}

	private void dfstraverse(IWalkable node, String numbering) {
		if(!mLogger.isInfoEnabled()){
			return;
		}
		
		mSeenList.put(node, numbering);
		mWriter.println("Node " + numbering + ";Annotations: ");
		if (node.hasPayload()) {
			IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				for (Entry<String, IAnnotations> annotation : payload.getAnnotations().entrySet()) {
					mWriter.println("  " + annotation.getKey());
					for (Entry<String, Object> keyvalue : annotation.getValue().getAnnotationsAsMap().entrySet()) {
						mWriter.print("    " + keyvalue.getKey() + ": ");
						if (keyvalue.getValue() instanceof Term) {
							new PrintTerm().append(mWriter, (Term) keyvalue.getValue());
						} else {
							mWriter.print(keyvalue.getValue());
						}
						mWriter.println();
					}
				}
			}
		}

		List<IWalkable> newnodes = new ArrayList<IWalkable>();
		List<IWalkable> children = node.getSuccessors();
		int num = -1;
		// Add new nodes and detect back edges...
		for (IWalkable n : children) {
			String backedge = mSeenList.get(n);
			if (backedge != null)
				mWriter.println("Back edge from " + numbering + " to " + backedge);
			else {
				String newnumbering = numbering + "." + (++num);
				mSeenList.put(n, newnumbering);
				newnodes.add(n);
			}
		}
		for (IWalkable n : newnodes)
			dfstraverse(n, mSeenList.get(n));
	}

	@Override
	public boolean performedChanges() {
		return false;
	}
}
