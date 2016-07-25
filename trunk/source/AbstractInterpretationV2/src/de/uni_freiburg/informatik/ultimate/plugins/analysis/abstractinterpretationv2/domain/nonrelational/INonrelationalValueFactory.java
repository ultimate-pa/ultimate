package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

public interface INonrelationalValueFactory<V extends INonrelationalValue<V>> {
	V createTopValue();
}
