package synthesis;

import java.util.HashSet;
import java.util.Set;
import org.apache.commons.lang3.ArrayUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class Strategy {
	
	private Template disjunction;
	private int disjuncts;
	private int[] conjuncts;
	private int[][] relation;
	private Set<TermVariable> vars;
	private String name;
 	
	
	public Strategy(IIcfg<IcfgLocation> icfg) {
		disjuncts = 2;
		conjuncts = new int[] {1,2};
		relation = new int[][] {{1}, {1, 1}};
		vars = new HashSet<TermVariable>();
		name = "name";
		
		disjunction = new DisjunctionTemplate(disjuncts, conjuncts, relation, vars, name);
	}
	
	public void complicate() {
		disjuncts++;
		conjuncts = ArrayUtils.add(conjuncts, disjuncts);
		relation = ArrayUtils.add(relation, new int[disjuncts]);
	}
	
	
}
