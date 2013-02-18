package local.stalin.plugins.generator.localvariablerenamer;
import java.util.Set;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.model.IElement;
import local.stalin.model.boogie.ast.Axiom;
import local.stalin.model.boogie.ast.ConstDeclaration;
import local.stalin.model.boogie.ast.Declaration;
import local.stalin.model.boogie.ast.FunctionDeclaration;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.TypeDeclaration;
import local.stalin.model.boogie.ast.Unit;
import local.stalin.model.boogie.ast.VariableDeclaration;
import local.stalin.model.boogie.ast.wrapper.WrapperNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class LocalVariableRenamerObserver implements IUnmanagedObserver {

//	private static Logger s_Logger = 
//				StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	public static final String SEPARATOR = "I";
	
	WrapperNode graphroot;
	
	@Override
	public boolean process(IElement root) {
		if (root instanceof WrapperNode) {

//			ProcedureLocVarRenamer debugLIR = 
//				new ProcedureLocVarRenamer("");
//			debugLIR.setProcedureName("");
			Unit unit = (Unit) ((WrapperNode)root).getBacking();
			Declaration[] declarations = unit.getDeclarations();
			FindDuplicateLocVar findDuplicateLocVar = new FindDuplicateLocVar();
			for (int i=0;i<declarations.length;i++){
				if (declarations[i] instanceof TypeDeclaration
						|| declarations[i] instanceof FunctionDeclaration
						|| declarations[i] instanceof ConstDeclaration
						|| declarations[i] instanceof VariableDeclaration
						|| declarations[i] instanceof Axiom) {
				}
				else if (declarations[i] instanceof Procedure){
					Procedure proc = (Procedure) declarations[i];
					findDuplicateLocVar.setProcedureName(proc.getIdentifier());
					findDuplicateLocVar.walkProcedure(proc);
				}
			}
			Set<String> duplicates = findDuplicateLocVar.getDuplicates();
			
			ProcedureLocVarRenamer locIdentRenamer = 
				new ProcedureLocVarRenamer(SEPARATOR,duplicates);
			
			Declaration[] newDeclarations = unit.getDeclarations();
			for (int i=0;i<declarations.length;i++){
				if (declarations[i] instanceof TypeDeclaration
						|| declarations[i] instanceof FunctionDeclaration
						|| declarations[i] instanceof ConstDeclaration
						|| declarations[i] instanceof VariableDeclaration
						|| declarations[i] instanceof Axiom) {
					newDeclarations[i] = declarations[i];
				}
				else if (declarations[i] instanceof Procedure){
//					s_Logger.debug("Found Procedure " + declarations[i]);
					Procedure proc = (Procedure) declarations[i];
//					s_Logger.debug("Found Procedure " + debugLIR.walkProcedure(proc));
//					assert(proc.toString().equals(debugLIR.walkProcedure(proc).toString()));
					locIdentRenamer.setProcedureName(proc.getIdentifier());
					newDeclarations[i] = locIdentRenamer.walkProcedure(proc);
//					s_Logger.debug("Renamed Procedure to " + declarations[i]);
					
				}
			}
			Unit newUnit = new Unit(newDeclarations);
			graphroot = new WrapperNode(null, newUnit);
		}
		else {
			return true;
		}
		return false;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

}
