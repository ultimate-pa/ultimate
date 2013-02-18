package de.uni_freiburg.informatik.ultimate.plugins.kojak;

import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.Predicate;

public class KojakProgramPoint extends ProgramPoint{

	/**
	 * 
	 */
	private static final long serialVersionUID = -8441204445155494284L;

	public KojakProgramPoint(String position, String procedure,
			boolean isErrorLoc, ASTNode astNode) {
		super(position, procedure, isErrorLoc, astNode, null, null);
	}
	
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof KojakProgramPoint) {
			if (obj == this)
				return true;
		}
		return false;
	}
	
	@Override
	public int hashCode() {
		return this.getPayload().hashCode();
	}
	
	public Predicate getPredicate() {
		IAnnotations annotation = this.getPayload().getAnnotations().get("kojak");
		Predicate predicate = annotation!=null?
				((KojakAnnotations)annotation).getPredicate():null;
		if(predicate == null) {
			if (this.isErrorLocation()) {
				predicate = KojakEngine.getFalsePredicate();
				setPredicateInKojakAnnotation(predicate);
			} else {
				predicate = KojakEngine.getTruePredicate();
				setPredicateInKojakAnnotation(predicate);
			}
		}
		return predicate;
	}
	
	public void initKojakAnnotation(Predicate predicate) {
		KojakAnnotations kojakAnnotations = new KojakAnnotations();
		kojakAnnotations.setPredicate(predicate);
		this.getPayload().getAnnotations().put("kojak", kojakAnnotations);
	}
	
	public void setPredicateInKojakAnnotation(Predicate predicate) {
		KojakAnnotations kojakAnnotations =
				(KojakAnnotations)this.getPayload().getAnnotations().get("kojak");
		if(kojakAnnotations == null) {
			initKojakAnnotation(predicate);
		} else {
			kojakAnnotations.setPredicate(predicate);
		}
	}
}
