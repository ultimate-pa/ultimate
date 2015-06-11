package de.uni_freiburg.informatik.ultimate.model.annotation;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * 
 * Types that implement {@link IElement} can mark instance fields with this
 * attribute. If a member is marked, Ultimate's debug visualization will display
 * the name of the field along with its value in the NodeView. The value is
 * obtained by calling {@link #toString()} on the field if it is not null, or by
 * invoking {@link String#valueOf(Object)}.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
@Target(ElementType.FIELD)
@Retention(RetentionPolicy.RUNTIME)
public @interface Visualizable {

}
