import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.border.Border;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;

/**
 *
 * @author Aurora
 */
public class CrosswordPanel extends WordlePanel {

    /*@
    invariant OUTLINE != null;
    invariant guessRows != null;
    invariant guessRows.length == wordleModel.MAX_GUESSES;
    invariant (\forall int i; i >= 0 && i < guessRows.length; guessRows[i] != null);
    invariant (\forall int i; i >= 0 && i < guessRows.length; guessRows[i].length == wordleModel.MAX_GUESS_LENGTH);
    */

    /**
     * The outline color for the guess panel.
     */
    public static Color OUTLINE = new Color(211, 214, 218);

    private JLabel[][] guessRows;

    /*@
    requires model != null;
    requires controller != null;
    ensures panelSize != null;
    ensures panelSize.width == 340;
    ensures panelSize.height == 380;
    */
    public CrosswordPanel(WordleModel model, WordleController controller){
        super(model, controller);
        super.panelSize = new Dimension(340,380);
        initGuessRows();
        addGuessRowsToPanel();
    }
    
    @Override
    public void updateState(){
        String guess = wordleModel.getGuessWord();
        int currentGuessTimes = wordleModel.getCurrentGuessTimes();
        JLabel currentGuessField;
        int COLOR_STATE;
        
        if(wordleModel.hasNewGameStarted()){
            clearGuessRows();
            return;
        }

        
        if(wordleModel.isGuessSubmitted()){
            for(int j = 0; j < wordleModel.MAX_GUESSWORD_LENGTH; j++){
                currentGuessField = guessRows[currentGuessTimes-1][j];
                COLOR_STATE = wordleModel.getGuessStateColor(j);
                changeGuessFieldState(currentGuessField, COLOR_STATE);
            }
            return;
        }

        for (int j = 0; j < wordleModel.MAX_GUESSWORD_LENGTH; j++){
            currentGuessField = guessRows[currentGuessTimes][j];
            if (j < guess.length()){
                currentGuessField.setText(Character.toString(guess.toUpperCase().charAt(j)));
                changeGuessFieldState(currentGuessField, wordleModel.NO_STATE);
            }
            else {
                clearGuessField(currentGuessField);
            }
        }
        
    }

    /*@
    ensures guessRows != null;
    ensures guessRows.length == wordleModel.MAX_GUESSES;
    ensures (\forall int i; i >= 0 && i < guessRows.length; guessRows[i] != null);
    ensures (\forall int i; i >= 0 && i < guessRows.length; guessRows[i].length == wordleModel.MAX_GUESS_LENGTH);
    */
    private void initGuessRows(){
        guessRows = new JLabel[wordleModel.MAX_GUESS_TIMES][wordleModel.MAX_GUESSWORD_LENGTH];
        for(int row = 0; row < wordleModel.MAX_GUESS_TIMES; row++){
            for(int col = 0; col < wordleModel.MAX_GUESSWORD_LENGTH; col++ ){
                guessRows[row][col] = createGuessField("");
            }
        }
    }

    /*@
    ensures (\forall int i; i >= 0 && i < guessRows.length; guessRows[i] != null);
    ensures (\forall int i; i >= 0 && i < guessRows.length; guessRows[i].length == wordleModel.MAX_GUESS_LENGTH);
    ensures (\forall int i, j; i >= 0 && i < guessRows.length && j >= 0 && j < wordleModel.MAX_GUESS_LENGTH; guessRows[i][j] != null);
    */
    private void addGuessRowsToPanel(){
        //guessPanel.setBorder(BorderFactory.createTitledBorder("guess"));
        for(int i = 0; i < guessRows.length; i++)
            for(int j = 0; j < wordleModel.MAX_GUESSWORD_LENGTH; j++)
                this.add(guessRows[i][j]);
    }

    /*@
    ensures \result != null;
    ensures \result.getPreferredSize() != null;
    ensures \result.getPreferredSize().width == 55;
    ensures \result.getPreferredSize().height == 55;
    ensures \result.getFont() != null;
    ensures \result.getFont().getStyle() == Font.BOLD;
    ensures \result.getFont().getSize() == 30;
    */
    private JLabel createGuessField(String text){
        JLabel field = new JLabel(text);
        field.setFont(new Font("Sans", Font.BOLD, 30));
        changeGuessFieldState(field, wordleModel.EMPTY_STATE);
        field.setPreferredSize(new Dimension(55,55));
        return field;
    }

    /*@
    requires currentGuessField != null;
    ensures currentGuessField.getText() == null;
    ensures \old(changeGuessFieldState) ==> (field.getBackground() == OUTLINE);
    ensures \old(changeGuessFieldState) ==> (field.getBorder() == compound);
    ensures \old(changeGuessFieldState) ==> (field.isOpaque() == true);
    ensures \old(changeGuessFieldState) ==> (field.getForeground() == Color.WHITE);
    ensures !\old(changeGuessFieldState) ==> (field.getBackground() == Color.LIGHT_GRAY);
    ensures !\old(changeGuessFieldState) ==> (field.getBorder() == compound);
    ensures !\old(changeGuessFieldState) ==> (field.isOpaque() == false);
    ensures !\old(changeGuessFieldState) ==> (field.getForeground() == null);
    */
    private void clearGuessField(JLabel currentGuessField) {
        currentGuessField.setText(null);
        changeGuessFieldState(currentGuessField, wordleModel.EMPTY_STATE);
    }

    /*@
    ensures (\forall int row; row >= 0 && row < wordleModel.MAX_GUESSES;
                (\forall int col; col >= 0 && col < wordleModel.MAX_GUESS_LENGTH;
                    guessRows[row][col].getText() == null));
    ensures (\forall int row; row >= 0 && row < wordleModel.MAX_GUESSES;
                (\forall int col; col >= 0 && col < wordleModel.MAX_GUESS_LENGTH;
                    guessRows[row][col].getBackground() == Color.LIGHT_GRAY));
    ensures (\forall int row; row >= 0 && row < wordleModel.MAX_GUESSES;
                (\forall int col; col >= 0 && col < wordleModel.MAX_GUESS_LENGTH;
                    guessRows[row][col].getBorder() == compound));
    ensures (\forall int row; row >= 0 && row < wordleModel.MAX_GUESSES;
                (\forall int col; col >= 0 && col < wordleModel.MAX_GUESS_LENGTH;
                    guessRows[row][col].isOpaque() == false));
    ensures (\forall int row; row >= 0 && row < wordleModel.MAX_GUESSES;
                (\forall int col; col >= 0 && col < wordleModel.MAX_GUESS_LENGTH;
                    guessRows[row][col].getForeground() == null));
    */
    private void clearGuessRows(){
        for(int row = 0; row < wordleModel.MAX_GUESS_TIMES; row++){
            for(int col = 0; col < wordleModel.MAX_GUESSWORD_LENGTH; col++ ){
                clearGuessField(guessRows[row][col]);
            }
        }
    }

    /*@
    requires field != null;
    requires state == wordleModel.GREEN_STATE || state == wordleModel.YELLOW_STATE ||
             state == wordleModel.GREY_STATE || state == wordleModel.NO_STATE ||
             state == wordleModel.EMPTY_STATE;
    ensures field.getBackground() == fillColor;
    ensures field.isOpaque() == (fillColor != null);
    ensures field.getForeground() == fontColor;
    ensures (borderColor != null) ==> (field.getBorder() == compound);
    ensures (borderColor == null) ==> (field.getBorder() == margin);
    */
    private void changeGuessFieldState(JLabel field, int state){
        if (state == wordleModel.GREEN_STATE)
            setFieldColor(field, null, GREEN, Color.WHITE);
        else if (state == wordleModel.YELLOW_STATE)
            setFieldColor(field, null, YELLOW, Color.WHITE);
        else if (state == wordleModel.GREY_STATE)
            setFieldColor(field, null, Color.DARK_GRAY, Color.WHITE);
        else if (state == wordleModel.NO_STATE)
            setFieldColor(field,Color.GRAY, null, Color.GRAY);
        else if (state == wordleModel.EMPTY_STATE)
            /*setFieldColor(field,Color.LIGHT_GRAY, null, null);*/
            setFieldColor(field,OUTLINE, null, null);
    }

    /*@
    requires field != null;
    requires borderColor == null || fillColor == null || fontColor == null;
    ensures field.getBackground() == fillColor;
    ensures field.isOpaque() == (fillColor != null);
    ensures field.getForeground() == fontColor;
    ensures (borderColor != null) ==> (field.getBorder() == compound);
    ensures (borderColor == null) ==> (field.getBorder() == margin);
    */
    private void setFieldColor(JLabel field, Color borderColor, 
            Color fillColor, Color fontColor){
        
        field.setBackground(fillColor);
        boolean isOpaque = fillColor != null;
        field.setOpaque(isOpaque);
        field.setForeground(fontColor);
        int borderThickness = 2;
        Border line;
        line = (borderColor != null) ? BorderFactory.createLineBorder(borderColor, 
                borderThickness) : null;
        Border margin = new EmptyBorder(0, 16, 0, 0);
        Border compound = new CompoundBorder(line, margin);
        field.setBorder(compound);
    }
}
