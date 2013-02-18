/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.TriggerExecutionContext.ReactivationContext;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.CuckooHashSet;

public class RCSet 
extends CuckooHashSet<TriggerExecutionContext.ReactivationContext> {
	
	private TriggerExecutionContext.ReactivationContext getStash(CCTerm match) {
		StashList<ReactivationContext> stash = stashList;
		while (stash != null) {
			if (stash.getEntry().equals(match))
				return stash.getEntry();
			stash = stash.getNext();
		}
		return null;
	}
	
	public TriggerExecutionContext.ReactivationContext get(CCTerm match) {
		int hash = hash(match);
		int hash1 = hash1(hash);
		ReactivationContext bucket = 
			(ReactivationContext) buckets[hash1]; 
  		if (bucket != null && bucket.equals(match))
			return bucket;
		bucket = (ReactivationContext) buckets[hash2(hash) ^ hash1]; 
  		if (bucket != null && bucket.equals(match))
			return bucket;
		return stashList != null ? getStash(match) : null;
	}
}
