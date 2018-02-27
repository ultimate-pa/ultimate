package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class BoogieTypeHelper {

	public BoogieType getBoogieTypeForBoogieASTType(final ASTType asttype) {
		final BoogieType result = (BoogieType) asttype.getBoogieType();
		assert result != null;
		return result;
	}

	/**
	 * Return a Boogie type for our internal AST type $Pointer$
	 *
	 * @return
	 */
	public BoogieType getBoogieTypeForPointerType() {
		//TODO
		throw new AssertionError("TODO: implement");
	}

	public IdentifierExpression constructIdentifierExpressionForHeapDataArray(final ILocation loc,
			final HeapDataArray hda, final String readProcedureName) {
		return ExpressionFactory.constructIdentifierExpression(loc, getBoogieTypeForBoogieASTType(hda.getASTType()),
				hda.getName(), new DeclarationInformation(StorageClass.GLOBAL, readProcedureName));
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
		return ExpressionFactory.constructIdentifierExpression(loc, boogieType, id,
				new DeclarationInformation(storageClass, surroundingProcedureName));
	}



}
