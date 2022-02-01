/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 * 
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;

public abstract class RCFGEdgeAnnotation extends AbstractAnnotations{

	private static final long serialVersionUID = 1L;
	
	protected IcfgEdge mBackingEdge;

	protected RCFGEdgeAnnotation(IcfgEdge backingEdge){
		mBackingEdge = backingEdge;
	}
	
	public IcfgEdge getBackingEdge() {
		return mBackingEdge;
	}
	
	@Override
	public boolean equals(Object obj) {
		if(obj instanceof RCFGEdgeAnnotation){
			return mBackingEdge.equals(((RCFGEdgeAnnotation)obj).mBackingEdge);
		} else if (obj instanceof IcfgEdge){
			return mBackingEdge.equals(obj);
		}
		return super.equals(obj);
	}
	
	@Override
	public int hashCode() {
		return mBackingEdge.hashCode();
	}
	
	@Override
	public String toString() {
		return mBackingEdge.toString();
	}

}
