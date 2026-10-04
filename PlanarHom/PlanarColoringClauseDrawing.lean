import PlanarHom.PlanarColoringClauseDrawingRows0
import PlanarHom.PlanarColoringClauseDrawingRows1
import PlanarHom.PlanarColoringClauseDrawingRows2
import PlanarHom.PlanarColoringClauseDrawingRows3
import PlanarHom.PlanarColoringClauseDrawingRows4
import PlanarHom.PlanarColoringClauseDrawingRows5
import PlanarHom.PlanarColoringClauseDrawingRows6
import PlanarHom.PlanarColoringClauseDrawingRows7
import PlanarHom.PlanarColoringClauseDrawingRows8
import PlanarHom.PlanarColoringClauseDrawingRows9
import PlanarHom.PlanarColoringClauseDrawingRows10
import PlanarHom.PlanarColoringClauseDrawingRows11
import PlanarHom.PlanarColoringClauseDrawingRows12
import PlanarHom.PlanarColoringClauseDrawingRows13
import PlanarHom.PlanarColoringClauseDrawingRows14
import PlanarHom.PlanarColoringClauseDrawingRows15

noncomputable section
namespace PlanarHom.PlanarColoringClause
open MultiGraph
set_option maxHeartbeats 5000000
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000

theorem allDrawingRows (e : Edge) : DrawingRow e := by
  rcases e with v1 | v2
  · rcases v1 with ⟨v3,v4⟩
    fin_cases v3
    · rcases v4 with v5 | v6
      · rcases v5 with ⟨v7,v8⟩
        fin_cases v7
        · fin_cases v8
          · exact drawingRow0
          · exact drawingRow1
          · exact drawingRow2
          · exact drawingRow3
          · exact drawingRow4
          · exact drawingRow5
          · exact drawingRow6
          · exact drawingRow7
        · fin_cases v8
          · exact drawingRow8
          · exact drawingRow9
          · exact drawingRow10
          · exact drawingRow11
          · exact drawingRow12
          · exact drawingRow13
          · exact drawingRow14
          · exact drawingRow15
        · fin_cases v8
          · exact drawingRow16
          · exact drawingRow17
          · exact drawingRow18
          · exact drawingRow19
          · exact drawingRow20
          · exact drawingRow21
          · exact drawingRow22
          · exact drawingRow23
      · rcases v6 with ⟨v9,v10⟩
        cases v9
        · rcases v10 with v11 | v12
          · fin_cases v11
            · exact drawingRow24
            · exact drawingRow25
            · exact drawingRow26
            · exact drawingRow27
            · exact drawingRow28
            · exact drawingRow29
            · exact drawingRow30
            · exact drawingRow31
          · rcases v12 with v13 | v14
            · fin_cases v13
              · exact drawingRow32
              · exact drawingRow33
              · exact drawingRow34
              · exact drawingRow35
              · exact drawingRow36
              · exact drawingRow37
              · exact drawingRow38
              · exact drawingRow39
            · fin_cases v14
              · exact drawingRow40
              · exact drawingRow41
              · exact drawingRow42
              · exact drawingRow43
              · exact drawingRow44
              · exact drawingRow45
              · exact drawingRow46
              · exact drawingRow47
              · exact drawingRow48
              · exact drawingRow49
        · rcases v10 with v15 | v16
          · fin_cases v15
            · exact drawingRow50
            · exact drawingRow51
            · exact drawingRow52
            · exact drawingRow53
            · exact drawingRow54
            · exact drawingRow55
            · exact drawingRow56
            · exact drawingRow57
          · rcases v16 with v17 | v18
            · fin_cases v17
              · exact drawingRow58
              · exact drawingRow59
              · exact drawingRow60
              · exact drawingRow61
              · exact drawingRow62
              · exact drawingRow63
              · exact drawingRow64
              · exact drawingRow65
            · fin_cases v18
              · exact drawingRow66
              · exact drawingRow67
              · exact drawingRow68
              · exact drawingRow69
              · exact drawingRow70
              · exact drawingRow71
              · exact drawingRow72
              · exact drawingRow73
              · exact drawingRow74
              · exact drawingRow75
    · rcases v4 with v19 | v20
      · rcases v19 with ⟨v21,v22⟩
        fin_cases v21
        · fin_cases v22
          · exact drawingRow76
          · exact drawingRow77
          · exact drawingRow78
          · exact drawingRow79
          · exact drawingRow80
          · exact drawingRow81
          · exact drawingRow82
          · exact drawingRow83
        · fin_cases v22
          · exact drawingRow84
          · exact drawingRow85
          · exact drawingRow86
          · exact drawingRow87
          · exact drawingRow88
          · exact drawingRow89
          · exact drawingRow90
          · exact drawingRow91
        · fin_cases v22
          · exact drawingRow92
          · exact drawingRow93
          · exact drawingRow94
          · exact drawingRow95
          · exact drawingRow96
          · exact drawingRow97
          · exact drawingRow98
          · exact drawingRow99
      · rcases v20 with ⟨v23,v24⟩
        cases v23
        · rcases v24 with v25 | v26
          · fin_cases v25
            · exact drawingRow100
            · exact drawingRow101
            · exact drawingRow102
            · exact drawingRow103
            · exact drawingRow104
            · exact drawingRow105
            · exact drawingRow106
            · exact drawingRow107
          · rcases v26 with v27 | v28
            · fin_cases v27
              · exact drawingRow108
              · exact drawingRow109
              · exact drawingRow110
              · exact drawingRow111
              · exact drawingRow112
              · exact drawingRow113
              · exact drawingRow114
              · exact drawingRow115
            · fin_cases v28
              · exact drawingRow116
              · exact drawingRow117
              · exact drawingRow118
              · exact drawingRow119
              · exact drawingRow120
              · exact drawingRow121
              · exact drawingRow122
              · exact drawingRow123
              · exact drawingRow124
              · exact drawingRow125
        · rcases v24 with v29 | v30
          · fin_cases v29
            · exact drawingRow126
            · exact drawingRow127
            · exact drawingRow128
            · exact drawingRow129
            · exact drawingRow130
            · exact drawingRow131
            · exact drawingRow132
            · exact drawingRow133
          · rcases v30 with v31 | v32
            · fin_cases v31
              · exact drawingRow134
              · exact drawingRow135
              · exact drawingRow136
              · exact drawingRow137
              · exact drawingRow138
              · exact drawingRow139
              · exact drawingRow140
              · exact drawingRow141
            · fin_cases v32
              · exact drawingRow142
              · exact drawingRow143
              · exact drawingRow144
              · exact drawingRow145
              · exact drawingRow146
              · exact drawingRow147
              · exact drawingRow148
              · exact drawingRow149
              · exact drawingRow150
              · exact drawingRow151
    · rcases v4 with v33 | v34
      · rcases v33 with ⟨v35,v36⟩
        fin_cases v35
        · fin_cases v36
          · exact drawingRow152
          · exact drawingRow153
          · exact drawingRow154
          · exact drawingRow155
          · exact drawingRow156
          · exact drawingRow157
          · exact drawingRow158
          · exact drawingRow159
        · fin_cases v36
          · exact drawingRow160
          · exact drawingRow161
          · exact drawingRow162
          · exact drawingRow163
          · exact drawingRow164
          · exact drawingRow165
          · exact drawingRow166
          · exact drawingRow167
        · fin_cases v36
          · exact drawingRow168
          · exact drawingRow169
          · exact drawingRow170
          · exact drawingRow171
          · exact drawingRow172
          · exact drawingRow173
          · exact drawingRow174
          · exact drawingRow175
      · rcases v34 with ⟨v37,v38⟩
        cases v37
        · rcases v38 with v39 | v40
          · fin_cases v39
            · exact drawingRow176
            · exact drawingRow177
            · exact drawingRow178
            · exact drawingRow179
            · exact drawingRow180
            · exact drawingRow181
            · exact drawingRow182
            · exact drawingRow183
          · rcases v40 with v41 | v42
            · fin_cases v41
              · exact drawingRow184
              · exact drawingRow185
              · exact drawingRow186
              · exact drawingRow187
              · exact drawingRow188
              · exact drawingRow189
              · exact drawingRow190
              · exact drawingRow191
            · fin_cases v42
              · exact drawingRow192
              · exact drawingRow193
              · exact drawingRow194
              · exact drawingRow195
              · exact drawingRow196
              · exact drawingRow197
              · exact drawingRow198
              · exact drawingRow199
              · exact drawingRow200
              · exact drawingRow201
        · rcases v38 with v43 | v44
          · fin_cases v43
            · exact drawingRow202
            · exact drawingRow203
            · exact drawingRow204
            · exact drawingRow205
            · exact drawingRow206
            · exact drawingRow207
            · exact drawingRow208
            · exact drawingRow209
          · rcases v44 with v45 | v46
            · fin_cases v45
              · exact drawingRow210
              · exact drawingRow211
              · exact drawingRow212
              · exact drawingRow213
              · exact drawingRow214
              · exact drawingRow215
              · exact drawingRow216
              · exact drawingRow217
            · fin_cases v46
              · exact drawingRow218
              · exact drawingRow219
              · exact drawingRow220
              · exact drawingRow221
              · exact drawingRow222
              · exact drawingRow223
              · exact drawingRow224
              · exact drawingRow225
              · exact drawingRow226
              · exact drawingRow227
  · rcases v2 with v47 | v48
    · rcases v47 with ⟨v49,v50⟩
      fin_cases v49
      · fin_cases v50
        · exact drawingRow228
        · exact drawingRow229
        · exact drawingRow230
        · exact drawingRow231
        · exact drawingRow232
        · exact drawingRow233
        · exact drawingRow234
      · fin_cases v50
        · exact drawingRow235
        · exact drawingRow236
        · exact drawingRow237
        · exact drawingRow238
        · exact drawingRow239
        · exact drawingRow240
        · exact drawingRow241
      · fin_cases v50
        · exact drawingRow242
        · exact drawingRow243
        · exact drawingRow244
        · exact drawingRow245
        · exact drawingRow246
        · exact drawingRow247
        · exact drawingRow248
    · fin_cases v48
      · exact drawingRow249
      · exact drawingRow250
      · exact drawingRow251
      · exact drawingRow252
      · exact drawingRow253

def integerCertificate : IntegerStraightDrawing.Certificate graph integerPoint where
  injective := by decide +kernel
  nondegenerate e := (allDrawingRows e).2.2
  separated e := (allDrawingRows e).1
  avoids e := (allDrawingRows e).2.1

def drawing : PlaneDrawing graph := IntegerStraightDrawing.drawing integerCertificate

theorem planar : graph.Planar := ⟨drawing⟩

end PlanarHom.PlanarColoringClause
