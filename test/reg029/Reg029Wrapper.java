import java.util.Map;

/**
 * The Java back end uses properties
 * instead of environment variables.
 * This wrapper loads the env variables
 * into the standard set of properties.
 */
public class Reg029Wrapper {
  public static void main(String args[]) {
    Map<String, String> env = System.getenv();
    for (String key : env.keySet()) {
      System.setProperty(key, env.get(key));
    }
    reg029.main(args);
  }
}
