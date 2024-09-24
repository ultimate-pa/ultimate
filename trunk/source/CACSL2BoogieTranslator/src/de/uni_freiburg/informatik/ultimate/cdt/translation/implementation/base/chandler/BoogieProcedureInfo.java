/*
 * Copyright (C) 2013-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Contains information about a procedure in the target Boogie program.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
final class BoogieProcedureInfo {

	/**
	 * the procedure's name in the Boogie program
	 */
	private final String mProcedureName;

	private CFunction mCType;

	private Procedure mDeclaration;
	private Procedure mImplementation;

	private final Set<VariableLHS> mModifiedGlobals;

	private boolean mModifiedGlobalsIsUsedDefined;

	BoogieProcedureInfo(final String name) {
		mProcedureName = name;
		mModifiedGlobals = new LinkedHashSet<>();
	}

	/**
	 * replace the existing declaration with another (refined) one
	 *
	 * @param declaration
	 */
	public void resetDeclaration(final Procedure declaration) {
		assert declaration.getSpecification() != null;
		assert declaration.getBody() == null;
		mDeclaration = declaration;
	}

	public boolean hasDeclaration() {
		return mDeclaration != null;
	}

	public boolean hasImplementation() {
		return mImplementation != null;
	}

	public boolean hasCType() {
		return mCType != null;
	}

	public void addModifiedGlobals(final Collection<VariableLHS> varNames) {
		mModifiedGlobals.addAll(varNames);
	}

	public void addModifiedGlobal(final VariableLHS varName) {
		mModifiedGlobals.add(varName);
	}

	public CFunction getCType() {
		if (mCType == null) {
			throw new IllegalStateException("query hasCType before calling this");
		}
		return mCType;
	}

	/**
	 * Add a parameter to the current function.
	 */
	public void updateCFunctionAddParam(final CDeclaration param) {
		final CDeclaration[] newParams;
		if (hasCType()) {
			final CDeclaration[] oldParams = getCType().getParameterTypes();
			newParams = Arrays.copyOf(oldParams, oldParams.length + 1);
			newParams[newParams.length - 1] = param;
		} else {
			newParams = new CDeclaration[] { param };
		}
		updateCFunctionReplaceParams(newParams);
	}

	/**
	 * Replace all parameter of the current function with the specified ones.
	 */
	public void updateCFunctionReplaceParams(final CDeclaration[] params) {
		if (hasCType()) {
			mCType = mCType.newParameter(params);
		} else {
			mCType = CFunction.createEmptyCFunction().newParameter(params);
		}
	}

	public void updateCFunction(final CFunction funcType) {
		mCType = funcType;
	}

	public Procedure getDeclaration() {
		if (mDeclaration == null) {
			throw new IllegalStateException("query hasDeclaration() first");
		}
		return mDeclaration;
	}

	public void setDefaultDeclarationAndCType(final ILocation loc, final ASTType intType) {
		setDefaultDeclaration(loc, intType);
		mCType = CFunction.createDefaultCFunction();
	}

	/**
	 * Sets the Boogie declaration that corresponds to the C declaration "int foo()".
	 */
	void setDefaultDeclaration(final ILocation loc, final ASTType intType) {
		setDeclaration(new Procedure(loc, new Attribute[0], mProcedureName, new String[0], new VarList[0],
				new VarList[] { new VarList(loc, new String[] { SFO.RES }, intType) }, new Specification[0], null));
	}

	void setDeclaration(final Procedure declaration) {
		assert mDeclaration == null : "can only be set once!";
		assert declaration.getSpecification() != null;
		assert declaration.getBody() == null;
		mDeclaration = declaration;
	}

	public Procedure getImplementation() {
		return mImplementation;
	}

	void setImplementation(final Procedure implementation) {
		assert mImplementation == null : "can only be set once!";
		assert implementation.getSpecification() == null;
		assert implementation.getBody() != null;
		mImplementation = implementation;
	}

	public boolean isModifiedGlobalsIsUsedDefined() {
		return mModifiedGlobalsIsUsedDefined;
	}

	public void setModifiedGlobalsIsUsedDefined(final boolean modifiedGlobalsIsUsedDefined) {
		mModifiedGlobalsIsUsedDefined = modifiedGlobalsIsUsedDefined;
	}

	public String getProcedureName() {
		return mProcedureName;
	}

	public Set<VariableLHS> getModifiedGlobals() {
		return Collections.unmodifiableSet(mModifiedGlobals);
	}

	@Override
	public String toString() {
		return mProcedureName + " : " + mCType;
	}
}
