package synthesis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/* Contains a List of all edges and their source and target */
public class EdgeList {
	private ArrayList<EdgeListEntry> mlist;
	private Theory mtheory;
	private TreeMap<String, TermVariable> mbuildVariables;
	public EdgeList(IIcfg<IcfgLocation> icfg){
		mlist = new ArrayList<EdgeListEntry>();
		mbuildVariables = new TreeMap<String, TermVariable>();
		
		ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		Map<String, Map<DebugIdentifier, IcfgLocation>> i = icfg.getProgramPoints();
		for ( String j : i.keySet()){
				Map<DebugIdentifier, IcfgLocation> l = i.get(j);
			for ( DebugIdentifier k : l.keySet() ){
				IcfgLocation point = l.get(k);
				for( IcfgEdge edge :  point.getOutgoingEdges() ){
					processEdge(edge, mgdScript);
					System.out.println("Running");
				}
			}
		}
		System.out.println(mlist);
	}
	
	private void processEdge(IcfgEdge e, ManagedScript s){
		IcfgLocation target = e.getTarget();
		IcfgLocation source = e.getSource();
		TransFormula f = e.getTransformula();
		Term term = f.getFormula();
		Map<Term,Term> m = new HashMap<>();
		System.out.println("term old: " + term);
		 ArrayList<TermVariable> invars = new ArrayList<TermVariable>();
		 // Process invars
		 for(  IProgramVar in  : f.getInVars().keySet() ){
			 if (mtheory == null) { // initialize mtheory once
				 mtheory = in.getTerm().getTheory();
			}
		  // System.out.println("All Invars: " + f.getInVars());
		  TermVariable var = getVariable("v_" + in.toString() + "_old" ,s); //TODO ints or reals?
		  //System.out.println("in: " + in + " var: " + var);
		  m.put( f.getInVars().get(in), var);
		  // System.out.println(f.getInVars().get(in) + "  " + m);
		  
		  }
		 // Process outvars
		  for(  IProgramVar out  : f.getOutVars().keySet() ){
			 if (mtheory == null) {  // initialize mtheory once
				 mtheory = out.getTerm().getTheory();
			}
		  // System.out.println("All outvars: " + f.getOutVars());
		  TermVariable var = getVariable("v_" + out.toString() + "_new" ,s); //TODO ints or reals?
		  // System.out.println("out: " + out + " var: " + var);
		  m.put( f.getOutVars().get(out), var);
		  // System.out.println(f.getInVars().get(out) + "  " + m);
		  }
		 SubstitutionWithLocalSimplification subs = new SubstitutionWithLocalSimplification(s, m);
		 term = subs.transform(term);
		 System.out.println("term new: " + term + "\n");
		 mlist.add(new EdgeListEntry(source, target, term));
	}
	
	/* Returns a variable with the name str. if one already exists, returns it */
private TermVariable getVariable(String str, ManagedScript s){
	if( ! mbuildVariables.containsKey(str)) {
		TermVariable v = s.variable(str, mtheory.getNumericSort());
		mbuildVariables.put(str, v);
		//System.out.println(str);
	}
	return mbuildVariables.get(str);
}
}
