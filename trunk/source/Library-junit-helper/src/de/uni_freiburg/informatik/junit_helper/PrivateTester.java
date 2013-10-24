package de.uni_freiburg.informatik.junit_helper;

import java.lang.reflect.Field;
import java.lang.reflect.Method;

public class PrivateTester<T> {

	@SuppressWarnings("unchecked")
	public T call(Object instance, String methodName, Object... args) 
			throws PrivateInvocationException {
		
		Class<?> cls = instance.getClass();
		Method method;
		Object ret;
		
		try {
			
			method = cls.getDeclaredMethod(methodName, cls);
			method.setAccessible(true); 
			ret = method.invoke(instance, args);

		} catch (Exception e) {
			throw (PrivateInvocationException) 
				new PrivateInvocationException().initCause(e);
		}
		
		return (T)ret;
	}
	
	@SuppressWarnings("unchecked")
	public T getField(Object instance, String fieldName) 
			 throws PrivateInvocationException {
		
		Class<?> cls = instance.getClass();
		Field field;
		Object ret;
		
		try {
			
			field = cls.getDeclaredField(fieldName);
			field.setAccessible(true);
			ret = field.get(instance);
			
		} catch (Exception e) {
			throw (PrivateInvocationException)
				new PrivateInvocationException().initCause(e);
		}
		
		return (T) ret;
	}
	
}
