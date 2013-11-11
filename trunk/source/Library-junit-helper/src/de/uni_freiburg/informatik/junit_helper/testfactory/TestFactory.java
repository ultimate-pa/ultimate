package de.uni_freiburg.informatik.junit_helper.testfactory;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * This defines the TestFactory annotation that will be used by the custom runner.
 * 
 * The target says that this annotation can be used to annotate methods 
 * The retention policy RUNTIME says that we want to read this annotation at runtime with reflections. 
 * 
 * @author dietsch
 *
 */
@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
public @interface TestFactory {

}

