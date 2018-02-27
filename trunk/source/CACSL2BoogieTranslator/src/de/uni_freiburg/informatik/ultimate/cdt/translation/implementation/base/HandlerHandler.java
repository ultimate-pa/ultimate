/*
 * Copyright (C) 2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.BoogieTypeHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.FunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HandlerHandler {

	private ITypeHandler mTypeHandler;
	private MemoryHandler mMemoryHandler;
	private ExpressionTranslation mExpressionTranslation;
	private StructHandler mStructHandler;
	private ProcedureManager mProcedureManager;
	private FunctionHandler mFunctionHandler;
	private TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	private BoogieTypeHelper mBoogieTypeHelper;
	private INameHandler mNameHandler;
	private TypeSizes mTypeSizes;
	private CHandler mCHandler;


	public INameHandler getNameHandler() {
		return mNameHandler;
	}

	public void setNameHandler(final INameHandler nameHandler) {
		mNameHandler = nameHandler;
	}

	public BoogieTypeHelper getBoogieTypeHelper() {
		return mBoogieTypeHelper;
	}

	public void setTypeHandler(final ITypeHandler typeHandler) {
		mTypeHandler = typeHandler;
	}

	public void setMemoryHandler(final MemoryHandler memoryHandler) {
		mMemoryHandler = memoryHandler;
	}

	public void setExpressionTranslation(final ExpressionTranslation expressionTranslation) {
		mExpressionTranslation = expressionTranslation;
	}

	public void setStructHandler(final StructHandler structHandler) {
		mStructHandler = structHandler;
	}

	public void setProcedureManager(final ProcedureManager procedureManager) {
		mProcedureManager = procedureManager;
	}

	public void setFunctionHandler(final FunctionHandler functionHandler) {
		mFunctionHandler = functionHandler;
	}

	public void setTypeSizeAndOffsetComputer(final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer) {
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
	}

	public void setBoogieTypeHelper(final BoogieTypeHelper boogieTypeHelper) {
		mBoogieTypeHelper = boogieTypeHelper;
	}

	public TypeSizeAndOffsetComputer getTypeSizeAndOffsetComputer() {
		return mTypeSizeAndOffsetComputer;
	}

	public ProcedureManager getProcedureManager() {
		return mProcedureManager;
	}

	public FunctionHandler getFunctionHandler() {
		return mFunctionHandler;
	}

	public ITypeHandler getTypeHandler() {
		return mTypeHandler;
	}

	public MemoryHandler getMemoryHandler() {
		return mMemoryHandler;
	}

	public ExpressionTranslation getExpressionTranslation() {
		return mExpressionTranslation;
	}

	public StructHandler getStructHandler() {
		return mStructHandler;
	}

	public void setTypeSizes(final TypeSizes typeSizes) {
		mTypeSizes = typeSizes;
	}

	public TypeSizes getTypeSizes() {
		return mTypeSizes;
	}

	public void setCHandler(final CHandler cHandler) {
		mCHandler = cHandler;
	}

	public CHandler getCHandler() {
		return mCHandler;
	}
}
