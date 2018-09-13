package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationState;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class BoogieTypeHelper {

	private final ITypeHandler mTypeHandler;
	private final CTranslationState mHandlerHandler;

	public BoogieTypeHelper(final CTranslationState handlerHandler) {
		handlerHandler.setBoogieTypeHelper(this);
		mHandlerHandler = handlerHandler;
		mTypeHandler = handlerHandler.getTypeHandler();
	}

	public BoogieType getBoogieTypeForBoogieASTType(final ASTType asttype) {
		if (asttype == null) {
			return BoogieType.TYPE_ERROR;
		}
		final BoogieType result = (BoogieType) asttype.getBoogieType();
		assert result != null;
		return result;
	}

	/**
	 * Return a Boogie type for our internal AST type $Pointer$
	 *
	 * convenience method, just calls typeHandler
	 *
	 * @return
	 */
	public BoogieType getBoogieTypeForPointerType() {
		return mTypeHandler.getBoogiePointerType();
	}

	public BoogieType getBoogieTypeForSizeT() {
		return BoogieType.TYPE_INT;
	}

	/**
	 * Convenience method
	 *
	 * @param loc
	 * @param astType
	 * @param id
	 * @param storageClass
	 * @param surroundingProcedureName
	 * @return
	 */
	public IdentifierExpression constructIdentifierExpression(final ILocation loc, final ASTType astType,
			final String id, final StorageClass storageClass, final String surroundingProcedureName) {
		return ExpressionFactory.constructIdentifierExpression(loc, getBoogieTypeForBoogieASTType(astType), id,
				new DeclarationInformation(storageClass, surroundingProcedureName));
	}

	/**
	 * Convenience method
	 * @param loc
	 * @param boogieTypeForPointerType
	 * @param id
	 * @param implementationInparam
	 * @param dispatchingProcedureName
	 * @return
	 */
	public IdentifierExpression constructIdentifierExpression(final ILocation loc, final BoogieType boogieType,
			final String id, final StorageClass storageClass, final String surroundingProcedureName) {
		assert storageClass != StorageClass.GLOBAL || surroundingProcedureName == null;
		return ExpressionFactory.constructIdentifierExpression(loc, boogieType, id,
				new DeclarationInformation(storageClass, surroundingProcedureName));
	}

	public BoogieType getBoogieTypeForCType(final CType cTypeRaw) {
		final CType cType = cTypeRaw.getUnderlyingType();

		if (cType instanceof CPrimitive) {
			if (mTypeHandler.isBitvectorTranslation()) {
				final Integer byteSize = mHandlerHandler.getTypeSizes().getSize(((CPrimitive) cType).getType());
				return BoogieType.createBitvectorType(byteSize * 8);
			} else {
				switch (((CPrimitive) cType).getGeneralType()) {
				case FLOATTYPE:
					return BoogieType.TYPE_REAL;
				case INTTYPE:
					return BoogieType.TYPE_INT;
				case VOID:
					return BoogieType.TYPE_ERROR;
				default:
					throw new AssertionError();
				}
			}
		} else if (cType instanceof CPointer) {
			return getBoogieTypeForPointerType();
		} else if (cType instanceof CEnum) {
			return getBoogieTypeForCType(new CPrimitive(CPrimitives.INT));
		} else if (cType instanceof CArray) {

			// may have to change this from int to something depending on bitvector settings and stuff..
			final BoogieType[] indexTypes = new BoogieType[] {
					getBoogieTypeForCType(new CPrimitive(CPrimitives.UINT)) };

			final BoogieType valueType = getBoogieTypeForCType(((CArray) cType).getValueType());
			return BoogieType.createArrayType(0, indexTypes, valueType);
		} else if (cType instanceof CFunction) {
			return getBoogieTypeForPointerType();
		} else if (cType instanceof CStruct) {
			final CStruct cStructType = (CStruct) cType;
			final BoogieType [] boogieFieldTypes = new BoogieType[cStructType.getFieldCount()];
			for (int i = 0; i < cStructType.getFieldCount(); i++) {
				boogieFieldTypes[i] = getBoogieTypeForCType(cStructType.getFieldTypes()[i]);
			}
			return BoogieType.createStructType(cStructType.getFieldIds(), boogieFieldTypes);
		} else {
			throw new AssertionError("unknown type " + cType);
		}
	}

	public BoogieType getBoogieTypeForPointerComponents() {
		return getBoogieTypeForCType(mHandlerHandler.getExpressionTranslation().getCTypeOfPointerComponents());
	}



}
