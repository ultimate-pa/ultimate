/*
 * Copyright (C) 2016 Yu-Wen Chen 
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public abstract class EqNode implements IEqNodeIdentifier<EqNode, EqFunction> {
	
	protected final EqNodeFactory mEqNodeFactory;

	protected Set<IProgramVar> mVariables;
	
	/**
	 * Is true iff this EqNode's term only uses global program symbols.
	 */
	protected final boolean mIsGlobal;
	
	protected final boolean mIsConstant;

	private final String mProcedure;
	
	private Set<EqNode> mParents = new HashSet<>();

	protected Term mTerm;
	
	/**
	 * indicates whether the Term only contains the standard TermVariables belonging to the IProgramVars, or if it
	 * is "versioned".
	 */
	protected final boolean mTermIsVersioned;


	EqNode(boolean isGlobal, boolean isConstant, String procedure, EqNodeFactory eqNodeFactory) {
		assert isGlobal || procedure != null;
		mIsGlobal = isGlobal;
		mIsConstant = isConstant;
		mProcedure = procedure;
		mEqNodeFactory = eqNodeFactory;
		mTermIsVersioned = false;
	}

	public EqNode(boolean isGlobal, boolean isConstant, String procedure, Term versionedTerm, 
			EqNodeFactory eqNodeFactory) {
		assert isGlobal || procedure != null;
		mIsGlobal = isGlobal;
		mIsConstant = isConstant;
		mProcedure = procedure;
		mEqNodeFactory = eqNodeFactory;
		mTerm = versionedTerm;
		mTermIsVersioned = true;
	}

	/**
	 * Yields the parents of this node in the EqNode graph (where the edges mean "is applied to"/"is a function argument
	 *  of"). Can be used to obtain initial ccParents for the corresponding EqGraphNode.
	 */
	Set<EqNode> getParents() {
		return mParents;
	}
	
	public void addParent(EqNode parent) {
		mParents.add(parent);
	}

	public abstract boolean isLiteral();

	/**
	 * Is true iff this EqNode's term only uses global program symbols.
	 */
	public boolean isGlobal() {
		return mIsGlobal;
	}
	
	
	public boolean isConstant() {
		return mIsConstant;
	}

	public Set<IProgramVar> getVariables() {
		return mVariables;
	}

	public Term getTerm() {
		return mTerm;
	}
	
	/**
	 * Returns procedure that this EqNode is local to. null if it is global.
	 */
	public String getProcedure() {
		return mProcedure;
	}
}
