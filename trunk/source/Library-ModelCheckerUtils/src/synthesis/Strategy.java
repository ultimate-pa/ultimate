package synthesis;

import java.util.HashSet;
import java.util.Set;
import org.apache.commons.lang3.ArrayUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class Strategy {
	
	private DisjunctionTemplate mDisjunction;
	private int mDisjuncts;
	private int[] mConjuncts;
	private int[][] mRelation;
	private Set<TermVariable> mVars;
	private String mName;
 	
	
	public Strategy(IIcfg<IcfgLocation> icfg) {
		mDisjuncts = 2;
		mConjuncts = new int[] {1,2};
		mRelation = new int[][] {{1}, {1, 1}};
		mVars = new HashSet<TermVariable>();
		mName = "name";
		
		// I really don't know how to do this better
		Script s = icfg.getCfgSmtToolkit().getManagedScript().getScript();
		
		mDisjunction = new DisjunctionTemplate(s, mDisjuncts, mConjuncts, mRelation, mVars, mName);
	}
	
	public void complicate() {
		mDisjuncts++;
		mConjuncts = ArrayUtils.add(mConjuncts, mDisjuncts);
		mRelation = ArrayUtils.add(mRelation, new int[mDisjuncts]);
	}
	
	
}
