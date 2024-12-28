/**
 *
 * @author Aurora
 */
public class WordleGameGUI {
    //@ ensures \result != null;
    //@ pure
    public static void main(String[] args) {
        javax.swing.SwingUtilities.invokeLater(
            new Runnable() {
                //@ ensures \result != null;
                public void run () {createAndShowGUI();}
            }
        );
    }
    //@ requires \result != null;
    //@ ensures \result != null;
    //@ pure
    public static void createAndShowGUI() {
        WordleModel model = new WordleModel();
        WordleController controller = new WordleController(model);
        WordleView view = new WordleView(model, controller);
    }
}
