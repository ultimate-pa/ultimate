package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;


/**
 * Rename signature procedures specification n a way that it is compatible to
 * the implementation of the procedure. E.g. we have specification <br>
 * {@code procedure foo(x:int) returns (y:bool);}<br>
 * and an implementation<br>
 * {@code implementation foo(a:int) returns (b:bool)}<br>
 * then this class can be used to obtain a specification where x is renamed to a
 * and y is renamed to b.<br>
 * {@code procedure foo(x:int) returns (y:bool);}
 */
public class RenameProcedureSpec extends BoogieTransformer {
	HashMap<String, String> renaming;
	
	public RenameProcedureSpec() {
	}
	
	public void buildRenaming(VarList[] specVars, VarList[] implVars) {
		int j1 = 0, j2 = 0;
		String[] implIds = new String[0];

		/* Iterate through all spec variables */
		for (int i1 = 0; i1 < specVars.length; i1++) {
			String[] specIds = specVars[i1].getIdentifiers();
			for (int i2 = 0; i2 < specIds.length; i2++) {

				/* Find next implementation variable */
				while (j2 == implIds.length) {
					implIds = implVars[j1++].getIdentifiers();
					j2 = 0;
				}
				
				assert specVars[i1].getType().getBoogieType()
					.equals(implVars[j1-1].getType().getBoogieType());
				if (!specIds[i2].equals(implIds[j2]))
					renaming.put(specIds[i2], implIds[j2]);
				j2++;
			}
		}
		return;
	}		
	
	public Specification[] renameSpecs(Procedure proc, Procedure impl) {
		Specification[] oldSpecs = proc.getSpecification();
		Specification[] specs = oldSpecs.clone();
		boolean changed = false;

		/* Put the input variables into renaming */
		renaming = new HashMap<String,String>();
		buildRenaming(proc.getInParams(), impl.getInParams());
		if (renaming.size() > 0) {
			/* Process the requires specifications only on in variables */
			for (int i = 0; i < specs.length; i++) {
				if (specs[i] instanceof RequiresSpecification) {
					specs[i] = processSpecification(specs[i]);
					if (specs[i] != oldSpecs[i])
						changed = true;
				}
			}
		}

		/* Now add the output variables to renaming */
		buildRenaming(proc.getOutParams(), impl.getOutParams());
		if (renaming.size() > 0) {
			/* Process the ensures specifications only on in and out variables */
			for (int i = 0; i < specs.length; i++) {
				if (specs[i] instanceof EnsuresSpecification) {
					specs[i] = processSpecification(specs[i]);
					if (specs[i] != oldSpecs[i])
						changed = true;
				}
			}
		}
		renaming = null;
		return changed ? specs : oldSpecs;
	}
	
	@Override
	public Expression processExpression(Expression expr) {
		/* TODO: handle name conflicts in quantifiers */
		if (expr instanceof IdentifierExpression) {
			IdentifierExpression id = (IdentifierExpression) expr;
			String newName = renaming.get(id.getIdentifier());
			if (newName != null) {
			    IdentifierExpression newExpr = new IdentifierExpression(
			    		expr.getLocation(), expr.getType(), newName, 
			    		id.getDeclarationInformation());
			    ModelUtils.mergeAnnotations(expr, newExpr);
			    return newExpr;
			}
			return expr;
		} else
			return super.processExpression(expr);
	}
}
