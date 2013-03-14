package de.uni_freiburg.informatik.ultimate.irs.dependencies.rcfg.annotations;

import de.uni_freiburg.informatik.ultimate.irs.dependencies.Activator;
import de.uni_freiburg.informatik.ultimate.model.AbstractAnnotations;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public abstract class IRSDependenciesAnnotation extends AbstractAnnotations {

	private static final long serialVersionUID = 1L;

	@SuppressWarnings("unchecked")
	public static <T extends IRSDependenciesAnnotation> T getAnnotation(
			IElement e, Class<?> c) {
		if (e.hasPayload()) {
			Object rtr = e.getPayload().getAnnotations()
					.get(Activator.PLUGIN_ID + c.getName());
			if (rtr != null) {
				return (T) rtr;
			}
		}
		return null;
	}

	public void addAnnotation(IElement e) {
		e.getPayload().getAnnotations()
				.put(Activator.PLUGIN_ID + this.getClass().getName(), this);
	}

}