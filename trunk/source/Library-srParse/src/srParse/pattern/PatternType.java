package srParse.pattern;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import pea.BooleanDecision;
import pea.CDD;
import pea.PhaseEventAutomata;
import pea.reqCheck.PatternToPEA;
import srParse.srParseScope;

public class PatternType
{
	//contains all CDDs from the patter in reverse order
	protected Vector<CDD> cdds;
	
	protected static CDD q_cdd_default = BooleanDecision.create("Q");
	protected static CDD r_cdd_default = BooleanDecision.create("R");
	protected int duration;
	protected PhaseEventAutomata pea;
	protected int effectOffset;
	
	protected srParseScope scope;
	protected PatternToPEA peaTransformator;
	
	public PatternType(){}
	public PatternType(srParseScope scope){
		setScope( scope );
	}
	
	protected CDD effect;
	
	/***
	 * Requirement has an effect on a set of Variables such as 
	 * @param effectOffset is the number of the effect phase counted from the last phase (most times -3 
	 * with upper bounds -2, -1 is always the last [true] phase)
	 * @example:  "After Q, it is always the case that if P holds then S holds". (t;[Q];t;[P && !S];t)
	 * Effect is S in this case
	 */
	public void setEffect(CDD effect, int effectOffset){
		this.effect = effect;
		assert(effectOffset > 0);
		this.effectOffset = effectOffset;
	}
	public void setEffect(CDD effect){
		this.effect = effect;
		this.effectOffset = 3; // default for all untimed non Before patterns.
	}
	public int getEffectOffset(){
		return this.effectOffset;
	}
	/***
	 * Determine if a variable name is in the set of variables that are affected by the requirement.
	 * @param ident
	 * 	identifier of variable
	 * @return
	 * 	true if the Variable's value is determined by this requirements effect.
	 */
	public boolean isEffect(String ident){
		return effect.getIdents().contains(ident);
	}
	public Set<String> getEffectVariabels(){
		return this.effect.getIdents();
	}
	public CDD getEffect(){
		return this.effect;
	}
	
	public int getDuration() {
		return duration;
	}
	
	public Vector<CDD> getCdds() {
		return cdds;
	}

	public void setDuration(int duration) {
		this.duration = duration;
	}
	
	protected CDD getDefaultQ_cdd() {
		return q_cdd_default;
	}

	protected CDD getDefaultR_cdd() {
		return r_cdd_default;
	}
	
	public void transform(){
		throw new UnsupportedOperationException();
	}
	
	public Vector<Integer> getElemHashes()
	{
		int i;
    	Vector<Integer> res=new Vector<Integer>();
    	
    	for( i=0;i<cdds.size();i++ ){
    		res.addAll( cdds.get(i).getElemHashes() );
    	}
    	if( scope.getCdd1()!=null && scope.getCdd1()!= q_cdd_default && scope.getCdd1()!= r_cdd_default){
			res.addAll( scope.getCdd1().getElemHashes() );
		}
    	if( scope.getCdd2()!=null && scope.getCdd2()!= q_cdd_default && scope.getCdd2()!= r_cdd_default ){
			res.addAll( scope.getCdd2().getElemHashes() );
		}
    	return res;
	}
	
	public void mergeCDDs( Vector<CDD> cdds )
	{
		int i;
		
		if( cdds==null )
			return;
		if( this.cdds==null )
			this.cdds=new Vector<CDD>();	
		for(i=0;i<cdds.size();i++){
			this.cdds.add(cdds.get(i));
		}
	}
	
	
	public PhaseEventAutomata transformToPea(){
		this.transform();
		return pea;
	}
	
	public PatternToPEA getPeaTransformator() {
		return peaTransformator;
	}

	public void setPeaTransformator(PatternToPEA peaTransformator) {
		this.peaTransformator = peaTransformator;
	}
	
	public srParseScope getScope() {
		return scope;
	}

	public void setScope(srParseScope scope) {
		this.scope = scope;
	}		

	public String toString(){
		String res=new String();
		res=scope.toString()+this.getClass().toString();
		return res;
	}
}








