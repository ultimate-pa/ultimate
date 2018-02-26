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
