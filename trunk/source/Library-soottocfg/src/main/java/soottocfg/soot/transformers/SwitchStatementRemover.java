/**
 * 
 */
package soottocfg.soot.transformers;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import soot.Body;
import soot.BodyTransformer;
import soot.PatchingChain;
import soot.Unit;
import soot.jimple.Expr;
import soot.jimple.IntConstant;
import soot.jimple.Jimple;
import soot.jimple.LookupSwitchStmt;
import soot.jimple.SwitchStmt;
import soot.jimple.TableSwitchStmt;

/**
 * @author schaef
 *
 */
public class SwitchStatementRemover extends BodyTransformer {

	/**
	 * 
	 */
	public SwitchStatementRemover() {
		// TODO Auto-generated constructor stub
	}

	/* (non-Javadoc)
	 * @see soot.BodyTransformer#internalTransform(soot.Body, java.lang.String, java.util.Map)
	 */
	@Override
	protected void internalTransform(Body body, String arg1, Map<String, String> arg2) {
			
		Map<Unit,List<Unit>> toReplace = new LinkedHashMap<Unit,List<Unit>>();
		
		PatchingChain<Unit> units = body.getUnits();
		for (Unit u : units) {
			if (u instanceof SwitchStmt) {
				toReplace.put(u, replaceSwitchStatement((SwitchStmt) u));
			}
		}
		for (Entry<Unit,List<Unit>> entry : toReplace.entrySet()) {
			units.insertAfter(entry.getValue(), entry.getKey());
			units.remove(entry.getKey());
		}
		body.validate();
		
	}
	
	/**
	 * Replace a SwitchStatement by a sequence of IfStmts and a Goto for the default case.
	 * @param s
	 * @return
	 */
	private List<Unit> replaceSwitchStatement(SwitchStmt s) {
		List<Unit> result = new LinkedList<Unit>();
		
		List<Expr> cases = new LinkedList<Expr>();
		List<Unit> targets = new LinkedList<Unit>();
		Unit defaultTarget = s.getDefaultTarget();
		
		if (s instanceof TableSwitchStmt) {
			TableSwitchStmt arg0 = (TableSwitchStmt)s;			
			int counter = 0;
			for (int i = arg0.getLowIndex(); i <= arg0.getHighIndex(); i++) {			
				cases.add(Jimple.v().newEqExpr(arg0.getKey(), IntConstant.v(i)));
				targets.add(arg0.getTarget(counter));
				counter++;
			}
		} else {
			LookupSwitchStmt arg0 = (LookupSwitchStmt)s;
			for (int i = 0; i < arg0.getTargetCount(); i++) {
				cases.add(Jimple.v().newEqExpr(arg0.getKey(), IntConstant.v(i)));
				targets.add(arg0.getTarget(i));
			}			
		}
		
		for (int i=0; i<cases.size(); i++) {
			result.add(Jimple.v().newIfStmt(cases.get(i), targets.get(i)));
		}
		if (defaultTarget!=null) {
			result.add(Jimple.v().newGotoStmt(defaultTarget));
		}
		return result;
	}

}
