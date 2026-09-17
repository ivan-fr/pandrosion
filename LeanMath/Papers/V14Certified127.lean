import LeanMath.Papers.V14Segments127_0
import LeanMath.Papers.V14Segments127_1
import LeanMath.Papers.V14Segments127_17
import LeanMath.Papers.V14Segments127_33
import LeanMath.Papers.V14Segments127_49
import LeanMath.Papers.V14Segments127_65
import LeanMath.Papers.V14Segments127_81
import LeanMath.Papers.V14Segments127_97
import LeanMath.Papers.V14Segments127_113
import LeanMath.Papers.V14Segments127_129
import LeanMath.Papers.V14Segments127_145
import LeanMath.Papers.V14Segments127_161
import LeanMath.Papers.V14Segments127_177
import LeanMath.Papers.V14Segments127_193
import LeanMath.Papers.V14Segments127_209
import LeanMath.Papers.V14Segments127_225
import LeanMath.Papers.V14Segments127_241
import LeanMath.Papers.V14Segments127_255
import LeanMath.Papers.V14DeployedUniform
noncomputable section
namespace LeanMath.Papers.V14Certified127
open Polynomial LeanMath.Papers.V14DeployedCoefficients LeanMath.Papers.V14DeployedAccumulation
open LeanMath.Papers.V14BernsteinCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def segments (i : ℕ) (hi : i<256) : Segment
    (LeanMath.Papers.V14RationalCertificate.numerator A127 (A127.comp (-X)) 127)
    (LeanMath.Papers.V14RationalCertificate.denominator A127 (A127.comp (-X)) 127)
    ((i:ℚ)*width127) (((i+1:ℕ):ℚ)*width127) (bounds127 i).1 (bounds127 i).2 := by
  interval_cases i
  · exact LeanMath.Papers.V14Segments127_0.segment0
  · exact LeanMath.Papers.V14Segments127_1.segment1
  · exact LeanMath.Papers.V14Segments127_1.segment2
  · exact LeanMath.Papers.V14Segments127_1.segment3
  · exact LeanMath.Papers.V14Segments127_1.segment4
  · exact LeanMath.Papers.V14Segments127_1.segment5
  · exact LeanMath.Papers.V14Segments127_1.segment6
  · exact LeanMath.Papers.V14Segments127_1.segment7
  · exact LeanMath.Papers.V14Segments127_1.segment8
  · exact LeanMath.Papers.V14Segments127_1.segment9
  · exact LeanMath.Papers.V14Segments127_1.segment10
  · exact LeanMath.Papers.V14Segments127_1.segment11
  · exact LeanMath.Papers.V14Segments127_1.segment12
  · exact LeanMath.Papers.V14Segments127_1.segment13
  · exact LeanMath.Papers.V14Segments127_1.segment14
  · exact LeanMath.Papers.V14Segments127_1.segment15
  · exact LeanMath.Papers.V14Segments127_1.segment16
  · exact LeanMath.Papers.V14Segments127_17.segment17
  · exact LeanMath.Papers.V14Segments127_17.segment18
  · exact LeanMath.Papers.V14Segments127_17.segment19
  · exact LeanMath.Papers.V14Segments127_17.segment20
  · exact LeanMath.Papers.V14Segments127_17.segment21
  · exact LeanMath.Papers.V14Segments127_17.segment22
  · exact LeanMath.Papers.V14Segments127_17.segment23
  · exact LeanMath.Papers.V14Segments127_17.segment24
  · exact LeanMath.Papers.V14Segments127_17.segment25
  · exact LeanMath.Papers.V14Segments127_17.segment26
  · exact LeanMath.Papers.V14Segments127_17.segment27
  · exact LeanMath.Papers.V14Segments127_17.segment28
  · exact LeanMath.Papers.V14Segments127_17.segment29
  · exact LeanMath.Papers.V14Segments127_17.segment30
  · exact LeanMath.Papers.V14Segments127_17.segment31
  · exact LeanMath.Papers.V14Segments127_17.segment32
  · exact LeanMath.Papers.V14Segments127_33.segment33
  · exact LeanMath.Papers.V14Segments127_33.segment34
  · exact LeanMath.Papers.V14Segments127_33.segment35
  · exact LeanMath.Papers.V14Segments127_33.segment36
  · exact LeanMath.Papers.V14Segments127_33.segment37
  · exact LeanMath.Papers.V14Segments127_33.segment38
  · exact LeanMath.Papers.V14Segments127_33.segment39
  · exact LeanMath.Papers.V14Segments127_33.segment40
  · exact LeanMath.Papers.V14Segments127_33.segment41
  · exact LeanMath.Papers.V14Segments127_33.segment42
  · exact LeanMath.Papers.V14Segments127_33.segment43
  · exact LeanMath.Papers.V14Segments127_33.segment44
  · exact LeanMath.Papers.V14Segments127_33.segment45
  · exact LeanMath.Papers.V14Segments127_33.segment46
  · exact LeanMath.Papers.V14Segments127_33.segment47
  · exact LeanMath.Papers.V14Segments127_33.segment48
  · exact LeanMath.Papers.V14Segments127_49.segment49
  · exact LeanMath.Papers.V14Segments127_49.segment50
  · exact LeanMath.Papers.V14Segments127_49.segment51
  · exact LeanMath.Papers.V14Segments127_49.segment52
  · exact LeanMath.Papers.V14Segments127_49.segment53
  · exact LeanMath.Papers.V14Segments127_49.segment54
  · exact LeanMath.Papers.V14Segments127_49.segment55
  · exact LeanMath.Papers.V14Segments127_49.segment56
  · exact LeanMath.Papers.V14Segments127_49.segment57
  · exact LeanMath.Papers.V14Segments127_49.segment58
  · exact LeanMath.Papers.V14Segments127_49.segment59
  · exact LeanMath.Papers.V14Segments127_49.segment60
  · exact LeanMath.Papers.V14Segments127_49.segment61
  · exact LeanMath.Papers.V14Segments127_49.segment62
  · exact LeanMath.Papers.V14Segments127_49.segment63
  · exact LeanMath.Papers.V14Segments127_49.segment64
  · exact LeanMath.Papers.V14Segments127_65.segment65
  · exact LeanMath.Papers.V14Segments127_65.segment66
  · exact LeanMath.Papers.V14Segments127_65.segment67
  · exact LeanMath.Papers.V14Segments127_65.segment68
  · exact LeanMath.Papers.V14Segments127_65.segment69
  · exact LeanMath.Papers.V14Segments127_65.segment70
  · exact LeanMath.Papers.V14Segments127_65.segment71
  · exact LeanMath.Papers.V14Segments127_65.segment72
  · exact LeanMath.Papers.V14Segments127_65.segment73
  · exact LeanMath.Papers.V14Segments127_65.segment74
  · exact LeanMath.Papers.V14Segments127_65.segment75
  · exact LeanMath.Papers.V14Segments127_65.segment76
  · exact LeanMath.Papers.V14Segments127_65.segment77
  · exact LeanMath.Papers.V14Segments127_65.segment78
  · exact LeanMath.Papers.V14Segments127_65.segment79
  · exact LeanMath.Papers.V14Segments127_65.segment80
  · exact LeanMath.Papers.V14Segments127_81.segment81
  · exact LeanMath.Papers.V14Segments127_81.segment82
  · exact LeanMath.Papers.V14Segments127_81.segment83
  · exact LeanMath.Papers.V14Segments127_81.segment84
  · exact LeanMath.Papers.V14Segments127_81.segment85
  · exact LeanMath.Papers.V14Segments127_81.segment86
  · exact LeanMath.Papers.V14Segments127_81.segment87
  · exact LeanMath.Papers.V14Segments127_81.segment88
  · exact LeanMath.Papers.V14Segments127_81.segment89
  · exact LeanMath.Papers.V14Segments127_81.segment90
  · exact LeanMath.Papers.V14Segments127_81.segment91
  · exact LeanMath.Papers.V14Segments127_81.segment92
  · exact LeanMath.Papers.V14Segments127_81.segment93
  · exact LeanMath.Papers.V14Segments127_81.segment94
  · exact LeanMath.Papers.V14Segments127_81.segment95
  · exact LeanMath.Papers.V14Segments127_81.segment96
  · exact LeanMath.Papers.V14Segments127_97.segment97
  · exact LeanMath.Papers.V14Segments127_97.segment98
  · exact LeanMath.Papers.V14Segments127_97.segment99
  · exact LeanMath.Papers.V14Segments127_97.segment100
  · exact LeanMath.Papers.V14Segments127_97.segment101
  · exact LeanMath.Papers.V14Segments127_97.segment102
  · exact LeanMath.Papers.V14Segments127_97.segment103
  · exact LeanMath.Papers.V14Segments127_97.segment104
  · exact LeanMath.Papers.V14Segments127_97.segment105
  · exact LeanMath.Papers.V14Segments127_97.segment106
  · exact LeanMath.Papers.V14Segments127_97.segment107
  · exact LeanMath.Papers.V14Segments127_97.segment108
  · exact LeanMath.Papers.V14Segments127_97.segment109
  · exact LeanMath.Papers.V14Segments127_97.segment110
  · exact LeanMath.Papers.V14Segments127_97.segment111
  · exact LeanMath.Papers.V14Segments127_97.segment112
  · exact LeanMath.Papers.V14Segments127_113.segment113
  · exact LeanMath.Papers.V14Segments127_113.segment114
  · exact LeanMath.Papers.V14Segments127_113.segment115
  · exact LeanMath.Papers.V14Segments127_113.segment116
  · exact LeanMath.Papers.V14Segments127_113.segment117
  · exact LeanMath.Papers.V14Segments127_113.segment118
  · exact LeanMath.Papers.V14Segments127_113.segment119
  · exact LeanMath.Papers.V14Segments127_113.segment120
  · exact LeanMath.Papers.V14Segments127_113.segment121
  · exact LeanMath.Papers.V14Segments127_113.segment122
  · exact LeanMath.Papers.V14Segments127_113.segment123
  · exact LeanMath.Papers.V14Segments127_113.segment124
  · exact LeanMath.Papers.V14Segments127_113.segment125
  · exact LeanMath.Papers.V14Segments127_113.segment126
  · exact LeanMath.Papers.V14Segments127_113.segment127
  · exact LeanMath.Papers.V14Segments127_113.segment128
  · exact LeanMath.Papers.V14Segments127_129.segment129
  · exact LeanMath.Papers.V14Segments127_129.segment130
  · exact LeanMath.Papers.V14Segments127_129.segment131
  · exact LeanMath.Papers.V14Segments127_129.segment132
  · exact LeanMath.Papers.V14Segments127_129.segment133
  · exact LeanMath.Papers.V14Segments127_129.segment134
  · exact LeanMath.Papers.V14Segments127_129.segment135
  · exact LeanMath.Papers.V14Segments127_129.segment136
  · exact LeanMath.Papers.V14Segments127_129.segment137
  · exact LeanMath.Papers.V14Segments127_129.segment138
  · exact LeanMath.Papers.V14Segments127_129.segment139
  · exact LeanMath.Papers.V14Segments127_129.segment140
  · exact LeanMath.Papers.V14Segments127_129.segment141
  · exact LeanMath.Papers.V14Segments127_129.segment142
  · exact LeanMath.Papers.V14Segments127_129.segment143
  · exact LeanMath.Papers.V14Segments127_129.segment144
  · exact LeanMath.Papers.V14Segments127_145.segment145
  · exact LeanMath.Papers.V14Segments127_145.segment146
  · exact LeanMath.Papers.V14Segments127_145.segment147
  · exact LeanMath.Papers.V14Segments127_145.segment148
  · exact LeanMath.Papers.V14Segments127_145.segment149
  · exact LeanMath.Papers.V14Segments127_145.segment150
  · exact LeanMath.Papers.V14Segments127_145.segment151
  · exact LeanMath.Papers.V14Segments127_145.segment152
  · exact LeanMath.Papers.V14Segments127_145.segment153
  · exact LeanMath.Papers.V14Segments127_145.segment154
  · exact LeanMath.Papers.V14Segments127_145.segment155
  · exact LeanMath.Papers.V14Segments127_145.segment156
  · exact LeanMath.Papers.V14Segments127_145.segment157
  · exact LeanMath.Papers.V14Segments127_145.segment158
  · exact LeanMath.Papers.V14Segments127_145.segment159
  · exact LeanMath.Papers.V14Segments127_145.segment160
  · exact LeanMath.Papers.V14Segments127_161.segment161
  · exact LeanMath.Papers.V14Segments127_161.segment162
  · exact LeanMath.Papers.V14Segments127_161.segment163
  · exact LeanMath.Papers.V14Segments127_161.segment164
  · exact LeanMath.Papers.V14Segments127_161.segment165
  · exact LeanMath.Papers.V14Segments127_161.segment166
  · exact LeanMath.Papers.V14Segments127_161.segment167
  · exact LeanMath.Papers.V14Segments127_161.segment168
  · exact LeanMath.Papers.V14Segments127_161.segment169
  · exact LeanMath.Papers.V14Segments127_161.segment170
  · exact LeanMath.Papers.V14Segments127_161.segment171
  · exact LeanMath.Papers.V14Segments127_161.segment172
  · exact LeanMath.Papers.V14Segments127_161.segment173
  · exact LeanMath.Papers.V14Segments127_161.segment174
  · exact LeanMath.Papers.V14Segments127_161.segment175
  · exact LeanMath.Papers.V14Segments127_161.segment176
  · exact LeanMath.Papers.V14Segments127_177.segment177
  · exact LeanMath.Papers.V14Segments127_177.segment178
  · exact LeanMath.Papers.V14Segments127_177.segment179
  · exact LeanMath.Papers.V14Segments127_177.segment180
  · exact LeanMath.Papers.V14Segments127_177.segment181
  · exact LeanMath.Papers.V14Segments127_177.segment182
  · exact LeanMath.Papers.V14Segments127_177.segment183
  · exact LeanMath.Papers.V14Segments127_177.segment184
  · exact LeanMath.Papers.V14Segments127_177.segment185
  · exact LeanMath.Papers.V14Segments127_177.segment186
  · exact LeanMath.Papers.V14Segments127_177.segment187
  · exact LeanMath.Papers.V14Segments127_177.segment188
  · exact LeanMath.Papers.V14Segments127_177.segment189
  · exact LeanMath.Papers.V14Segments127_177.segment190
  · exact LeanMath.Papers.V14Segments127_177.segment191
  · exact LeanMath.Papers.V14Segments127_177.segment192
  · exact LeanMath.Papers.V14Segments127_193.segment193
  · exact LeanMath.Papers.V14Segments127_193.segment194
  · exact LeanMath.Papers.V14Segments127_193.segment195
  · exact LeanMath.Papers.V14Segments127_193.segment196
  · exact LeanMath.Papers.V14Segments127_193.segment197
  · exact LeanMath.Papers.V14Segments127_193.segment198
  · exact LeanMath.Papers.V14Segments127_193.segment199
  · exact LeanMath.Papers.V14Segments127_193.segment200
  · exact LeanMath.Papers.V14Segments127_193.segment201
  · exact LeanMath.Papers.V14Segments127_193.segment202
  · exact LeanMath.Papers.V14Segments127_193.segment203
  · exact LeanMath.Papers.V14Segments127_193.segment204
  · exact LeanMath.Papers.V14Segments127_193.segment205
  · exact LeanMath.Papers.V14Segments127_193.segment206
  · exact LeanMath.Papers.V14Segments127_193.segment207
  · exact LeanMath.Papers.V14Segments127_193.segment208
  · exact LeanMath.Papers.V14Segments127_209.segment209
  · exact LeanMath.Papers.V14Segments127_209.segment210
  · exact LeanMath.Papers.V14Segments127_209.segment211
  · exact LeanMath.Papers.V14Segments127_209.segment212
  · exact LeanMath.Papers.V14Segments127_209.segment213
  · exact LeanMath.Papers.V14Segments127_209.segment214
  · exact LeanMath.Papers.V14Segments127_209.segment215
  · exact LeanMath.Papers.V14Segments127_209.segment216
  · exact LeanMath.Papers.V14Segments127_209.segment217
  · exact LeanMath.Papers.V14Segments127_209.segment218
  · exact LeanMath.Papers.V14Segments127_209.segment219
  · exact LeanMath.Papers.V14Segments127_209.segment220
  · exact LeanMath.Papers.V14Segments127_209.segment221
  · exact LeanMath.Papers.V14Segments127_209.segment222
  · exact LeanMath.Papers.V14Segments127_209.segment223
  · exact LeanMath.Papers.V14Segments127_209.segment224
  · exact LeanMath.Papers.V14Segments127_225.segment225
  · exact LeanMath.Papers.V14Segments127_225.segment226
  · exact LeanMath.Papers.V14Segments127_225.segment227
  · exact LeanMath.Papers.V14Segments127_225.segment228
  · exact LeanMath.Papers.V14Segments127_225.segment229
  · exact LeanMath.Papers.V14Segments127_225.segment230
  · exact LeanMath.Papers.V14Segments127_225.segment231
  · exact LeanMath.Papers.V14Segments127_225.segment232
  · exact LeanMath.Papers.V14Segments127_225.segment233
  · exact LeanMath.Papers.V14Segments127_225.segment234
  · exact LeanMath.Papers.V14Segments127_225.segment235
  · exact LeanMath.Papers.V14Segments127_225.segment236
  · exact LeanMath.Papers.V14Segments127_225.segment237
  · exact LeanMath.Papers.V14Segments127_225.segment238
  · exact LeanMath.Papers.V14Segments127_225.segment239
  · exact LeanMath.Papers.V14Segments127_225.segment240
  · exact LeanMath.Papers.V14Segments127_241.segment241
  · exact LeanMath.Papers.V14Segments127_241.segment242
  · exact LeanMath.Papers.V14Segments127_241.segment243
  · exact LeanMath.Papers.V14Segments127_241.segment244
  · exact LeanMath.Papers.V14Segments127_241.segment245
  · exact LeanMath.Papers.V14Segments127_241.segment246
  · exact LeanMath.Papers.V14Segments127_241.segment247
  · exact LeanMath.Papers.V14Segments127_241.segment248
  · exact LeanMath.Papers.V14Segments127_241.segment249
  · exact LeanMath.Papers.V14Segments127_241.segment250
  · exact LeanMath.Papers.V14Segments127_241.segment251
  · exact LeanMath.Papers.V14Segments127_241.segment252
  · exact LeanMath.Papers.V14Segments127_241.segment253
  · exact LeanMath.Papers.V14Segments127_241.segment254
  · exact LeanMath.Papers.V14Segments127_255.segment255

/-- Unconditional uniform relative error for the actual deployed p=127 rational function. -/
theorem uniform127 (y : ℝ) (hy : |y|≤rho127) :
    |(A127.eval y/A127.eval (-y))/(LeanMath.Papers.Cayley.unchi y)^(1/(127:ℝ))-1| <
      (60/100)/(2:ℝ)^52 :=
  LeanMath.Papers.V14DeployedUniform.uniform127_of_segments segments y hy

end LeanMath.Papers.V14Certified127
