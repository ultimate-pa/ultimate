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
		//TODO
		throw new AssertionError("TODO: implement");
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

}
