/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker plug-in.
 * 
 * The ULTIMATE LassoRanker plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 * Abstract Superclass for lasso extraction. Can be removed if there is only
 * one class that implements this.
 * @author Matthias Heizmann
 */
public abstract class AbstractLassoExtractor {
	protected NestedWord<CodeBlock> mStem;
	protected NestedWord<CodeBlock> mLoop;
	protected BoogieIcfgLocation mHonda;
	protected boolean mLassoFound;
	protected IcfgLocation mSomeNoneForErrorReport;
	
	public NestedWord<CodeBlock> getStem() {
		if (!mLassoFound) {
			throw new UnsupportedOperationException("no lasso was found");
		}
		return mStem;
	}

	public NestedWord<CodeBlock> getLoop() {
		if (!mLassoFound) {
			throw new UnsupportedOperationException("no lasso was found");
		}

		return mLoop;
	}

	public BoogieIcfgLocation getHonda() {
		if (!mLassoFound) {
			throw new UnsupportedOperationException("no lasso was found");
		}

		return mHonda;
	}

	public boolean wasLassoFound() {
		return mLassoFound;
	}

	public IcfgLocation getSomeNoneForErrorReport() {
		if (mLassoFound) {
			throw new UnsupportedOperationException(
					"lasso was found, there was no error");
		}
		return mSomeNoneForErrorReport;
	}
	
}
