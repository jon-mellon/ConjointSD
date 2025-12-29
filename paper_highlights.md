Abstract
Social status is a core aspect of societal inequalities, yet its determinants remain understudied.
W e investigate the factors that shape social status judgments in Great Britain using a conjoint
survey experiment with 7,680 respondents making 30,720 status assessments. Drawing on the
extant literature, we test economic (occupation, income, wealth, education, class background),
cultural (leisure activities and supermarket choice), and ascribed (gender and ethnicity) factors as
determinants of social status. Income has substantial positive effect, as do pro-social occupations
(teaching and healthcare). Cultural capital, measured through leisure activities and supermarket
preferences, plays a major role in status assessments. W e also find that housing wealth, private
schooling, higher education, and being White British all increase perceived status. W e also
contribute to our understanding of what factors distribute the most status by combining our
experimental estimates with data on the prevalence of status predictors in the British population.
W e find that economic factors, particularly income and wealth, have the largest impact on status
distribution. Cultural factors have a smaller effect, with ascribed characteristics like ethnicity
and gender distributing the least status across the whole population, despite sizeable individual-
level effects for ethnic minorities. Our findings support multiple sociological theories of status,
demonstrating the importance of occupation, economic resources, cultural capital, and racial
hierarchies in status judgments. However, economic factors dominate the distribution of status
across society .

4 Methods
4.1 Experimental design
Our experiment differs from previous approaches to finding the determinants of status by having respondents
make status judgments about hypothetical personas on the basis of many different attributes. Figure 1shows
an example of the experimental setup. Each respondent sees two sets of people to rate making for a total of
four judgments per respondent.2Each respondent saw two sets of two hypothetical personas, each with one
of 8,500 randomly assigned possible combinations of occupation,3income, schooling, housing, education4,
ethnicity5, gender, cultural consumption, and class background,6which they rated on a 0 (low status) to
100 (high status) scale to give around 30,720 status judgments in total.
Each of these attributes is independently randomized, which allows the causal effect of each to be estimated
simultaneously . This bypasses the problem faced by observational studies: differentiating sources of status
can be diﬀicult because all likely sources of status are correlated with one another (the view that they are
extremely highly correlated is often called homology (Bourdieu 1984, p175; Chan 2010)).
The order of attributes shown was randomized with the exception of parental occupation which is always
shown last (to avoid the confusion of showing it before a person’s own occupation). Respondents are then
asked to rate both of the hypothetical people on a continuous scale from “very low social standing” to “very
high social standing” . If they are unsure of the person’s social standing, they can drag the marker into the
“not sure” box.7
T o ensure that these personas were believable, we used a curated list of real job titles taken from the UK Oﬀice
for National Statistics Standard Occupational Classification 2010 (SOC2010) schema. W e then constrain
each random persona to have a plausible income range and level of educational attainment consistent with
their occupation. As such, our design allows us to identify average marginal component effects for the various
contributors to social status without sacrificing plausibility . F urther, since SOC2010 is a hierarchical schema
with occupations nested in units, minor, sub-major, and major occupational groupings, our design also allows
us to isolate the variation attributable to each level. This, in turn, allows us to determine occupational social
status hierarchies at varying levels of granularity , from individual jobs to large-scale occupational types.
W e generally randomly assigned attributes to personas in the experiment. However, some combinations of
occupation and income or education lacked external validity . F or instance, it is not clear what we learn by
asking people to rate an anesthetist earning £12,000 per year who has no qualifications. W e therefore limited
the income and educational ranges we could show for each occupation to plausible combinations. While this
breaks pure randomization, the design is still causally identified provided we include all randomized variables
as covariates in our design (because each variable is still conditionally random).8
By randomizing both occupation and income, we can avoid the critique levied at occupational prestige
scales that they simply noisily measure the economic position of occupations rather than measuring a
substantively meaningful dimension of status (F eatherman and Hauser 1976). Because we directly show
income, respondents do not need to make a separate (and potentially incorrect) inference about the income
level of an occupation. Instead, any judgments of the prestige of occupations in our experiment will reflect
the net impact of occupation above and beyond its effect on income.9
W e also included three leisure activities (from a list of 38 possible activities) as an indicator of embodied
cultural capital. W e measure cultural consumption through choice of supermarket. As in the US (F reeland
and Hoey 2018), British supermarkets have a strong social meaning with W aitrose and Marks & Spencer
generally considered to be “upmarket” and the lower cost Iceland and Lidl having a strong association as
“working class” shops.
W e randomized the wording of the status question to be either: 1) “How do you think people in general
would rate person 1 and person 2’s standing in society?” 2) “How would you rate person 1 and person 2’s
standing in society?” 3) “How much do you think people in general respect person 1 and person 2?”
These are assessments of a respondent’s perception of societal status and not a measure of how much
the respondent personally perceives the person as worthy of being high or low status. This means that
respondents, for instance, who think that ethnic minorities should have equal status to white British people
are reporting on how they think people from different ethnic groups are perceived in British society rather
than how the respondent thinks they should be perceived. This also means it is not necessarily a socially
desirable answer to say that people from ethnic minority groups are high status (as this could be seen as
denying the existence of persistent inequalities).
W e included the less direct “how do you think people in general would rate” wording to give an option that
further distances the respondent from their judgment if there were any residual social desirability effects.
W e included the “respect” wording to test whether our results fall into the critiques of occupational prestige
that they simply measure economic success rather than the more relational idea of prestige (Bukodi, Dex,
and Goldthorpe 2011; F eatherman and Hauser 1976). In appendix A1 , we show that none of our results
are substantively affected by these variant wordings, suggesting that all three wordings tap into the same
general concept at least in the context of this experimental setup. W e therefore pool the results of the three
wordings together for our analysis in this paper.
The logic of our experiment is to have respondents directly make status judgments of hypothetical people.
The external validity of this design is high because status is inherently a relational attribute assigned by
other people to someone on the basis of observations about them. While no survey experiment can capture
all the dimensions that status judgments will be made on, we aim to include the main ones that are broadly
applicable based on the existing literature discussed above.
The experiment was fielded on wave 21 of the British Election Study Internet Panel (BESIP) from 6th to
26th May 2022 (Fieldhouse et al. 2024).

4.2 Model specification and estimation
W e use Bayesian hierarchical linear regression models to estimate the effect of a persona’s characteristics
on the status judgment a respondent makes of them using the BRMS package (Bürkner 2017). As we
discuss above, our experimental design requires that we constrain each persona’s income and education to
be consistent with its occupation. But this introduces correlations between occupation and income and
occupation and education that, if not accounted for, would bias our estimates of the average marginal
component effect (AMCE) of income and education. In cases like this, where randomization is contingent,
Hainmueller, Hopkins, and Y amamoto (2014) suggest stratifying the data by group, calculating the group-
specific AMCEs, and then taking their weighted average to get the overall AMCE. Since we use hierarchical
regression, this is possible when fitting our model. T o do so, we need only include random slopes on
our income and education effects according to the four levels of the SOC2010 occupation hierarchy that
determines their range. The random slopes estimate group-wise treatment effects (with some partial pooling)
and these estimates are then averaged to produce a grand mean. As all occupations in our experiment have
an equal chance of occurring (and so have equal weights), this grand mean should, therefore, be equivalent
to the overall AMCE of income and education.
𝑦𝑖∼ 𝑁 𝑜𝑟𝑚𝑎𝑙(𝜇𝑖, 𝜎)
𝜇𝑖= 𝛼 + 𝛼𝑝𝑎𝑔𝑒[𝑖] + 𝛼𝑟𝑒𝑠𝑝𝑜𝑛𝑑𝑒𝑛𝑡[𝑖] + (1)
𝛼𝑢𝑛𝑖𝑡[𝑖] + 𝛼𝑚𝑖𝑛𝑜𝑟[𝑖] + 𝛼𝑠𝑢𝑏𝑚𝑎𝑗𝑜𝑟[𝑖] + 𝛼𝑚𝑎𝑗𝑜𝑟[𝑖] + (2)
𝛼𝑃 𝑢𝑛𝑖𝑡[𝑖] + 𝛼𝑃 𝑚𝑖𝑛𝑜𝑟[𝑖] + 𝛼𝑃 𝑠𝑢𝑏𝑚𝑎𝑗𝑜𝑟[𝑖] + 𝛼𝑃 𝑚𝑎𝑗𝑜𝑟[𝑖] + (3)
∑𝑗∈𝑙𝑒𝑖𝑠𝑢𝑟𝑒[𝑖](𝛼𝑙𝑒𝑖𝑠𝑢𝑟𝑒[𝑗] )
3+ (4)
+𝛽1𝑥1... + 𝛽𝑛𝑥𝑛 (5)
W e use a series of random intercepts for different aspects of the experiment. W e account for nuisance
variation in the form of respondent ( 𝛼𝑟𝑒𝑠𝑝𝑜𝑛𝑑𝑒𝑛𝑡[𝑖] ) and page ( 𝛼𝑝𝑎𝑔𝑒[𝑖] ) random intercepts.
W e model the effects of a persona’s occupation and the persona’s parent’s occupations hierarchically .
SOC2010 unit codes have 4 digits, with each successive unit providing more granularity . W e
therefore include separate random intercepts for the 4-digit unit-level ( 𝛼𝑢𝑛𝑖𝑡[𝑖] /𝛼𝑃 𝑢𝑛𝑖𝑡[𝑖] ), 3-digit minor
level ( 𝛼𝑚𝑖𝑛𝑜𝑟[𝑖] /𝛼𝑃 𝑚𝑖𝑛𝑜𝑟[𝑖] ), 2-digit sub-major level ( 𝛼𝑠𝑢𝑏𝑚𝑎𝑗𝑜𝑟[𝑖] /𝛼𝑃 𝑠𝑢𝑏𝑚𝑎𝑗𝑜𝑟[𝑖] ), and 1-digit major level
(𝛼𝑚𝑎𝑗𝑜𝑟[𝑖] /𝛼𝑃 𝑚𝑎𝑗𝑜𝑟[𝑖] ).
W e also model the leisure activities as a multi-membership random effects term 𝛼𝑙𝑒𝑖𝑠𝑢𝑟𝑒[𝑗] since each character
is shown with three leisure activities.
The priors are all normal (or folded-normal in the case of 𝜎𝑘)𝒩(𝜇, 𝜎) where 𝜇is the mean of the normal
distribution and 𝜎is the standard deviation of the distribution, making them weakly informative. Note that
these priors are defined on unscaled versions of the variables.
𝛽 ∼ 𝒩(0, 5) (6)
𝛼𝑘∼ 𝒩(0, 𝜎𝑘) (7)
𝜎𝑘∼ |𝒩(0, 5)| (8)

4.3 Predicting population status distributions
Our experiment as described so far allows us to establish how much different attributes affect status judgments
for a particular individual. However, we also want to know what factors play the largest role in distributing
status in society . F or this we need to know the prevalence and covariance of the different factors in the
population.
Our estimated models allow us to predict scores for real people based on their levels of the various attributes
that we included in the experiment. This then allows us to establish how much status scores vary across
a representative sample of the population. F or instance, we can establish what the standard deviation
of predicted status scores are across the British population. Importantly , however, it also allows us to
establish the standard deviation of predicted status scores attributable to different subsets of variables in
our experiment because we use linear models. F or instance, we can look at the standard deviation of predicted
status scores attributable to economic factors, or job factors, or just income.
F or instance, if we wanted to look at the standard deviation of social status due to gender we would first
predict status scores for all respondents in a representative sample based just on their gender ( 𝑔𝑒𝑛𝑑𝑒𝑟𝑖) and
the estimated coeﬀicient on gender from the experiment 𝛽1:
𝑠𝑡𝑎𝑡𝑢𝑠𝑔𝑒𝑛𝑑𝑒𝑟
𝑖 = 𝛽1𝑔𝑒𝑛𝑑𝑒𝑟𝑖
we then calculate the standard deviation of 𝑠𝑡𝑎𝑡𝑢𝑠𝑔𝑒𝑛𝑑𝑒𝑟
𝑖 attributable to people’s gender:
𝑠𝑑(𝑠𝑡𝑎𝑡𝑢𝑠𝑔𝑒𝑛𝑑𝑒𝑟
𝑖 )
In order to calculate these combined distributions of social status attributable to a set of factors, we need
the distribution of the variables of interest. W e cannot simply use oﬀicial statistics for this purpose because
we need the joint distribution of the variables. W e therefore use BESIP data (weighted to be representative
of the British population).
One challenge in translating our experimental estimates to a target population is how to use the leisure
activities items. In the experiment, all social status judgments were made on people who engaged in exactly
three leisure activities. However, our population survey asked respondents “Which of the following activities,
if any , have you participated in over the past 12 months? Please tick all that apply . ” . This means that most
respondents in the population have not engaged in exactly three leisure activities over the last 12 months
(on average respondents reported participating in 6.8 activities). Our main approach to estimating the
population distribution of status due to leisure activities is to take the average of a respondent’s leisure
activity effects and multiply it by three in order to scale it to the same level as the experiment. W e also
estimate a version of the status distributions where we apply the effects from the experiment directly to the
population data. However, we believe that this is likely to be an overestimate of the variability of status
attributable to leisure activities because it is applying estimates from an experiment where only three leisure
activities were shown to a distribution where many more activities were selected on average.
F or the desirability of an area, this was diﬀicult to assess directly . Our experiment gave the options of
“rundown”, “housing estate” (middle class housing), and “desirable area” . W e estimated the equivalents of
these based on five questions about a respondent’s area: level of crime; lack of community spirit; interesting
restaurants, bars, and shops; buildings and public spaces being well maintained; and local schools providing
high quality education. W e feed these into an graded response IR T model and cut the variable into quartiles.
W e assign the bottom quartile as rundown, the middle 2 quartiles and housing estate and the top quartile
as desirable area.

5 Results
F or each set of factors, we consider its effects in two ways. First, we show the effect size of each attribute
(shown in figure 3). Second, we show combinations of factors distribute status across Britain accounting for
the size of each attribute’s effect and the distribution of the factors being judged (figure 7). In line with the
conceptual map of status components in figure 2, we break status sources into three high-level categories of
economic, cultural, and ascribed. Finally , we predict
5.1 Effect sizes
5.1.1 Economic
Figure 4shows the effect of a persona being shown with different income levels on the average status
judgment that respondents made about them.11A verage status scores increase substantially between the
lowest individual incomes and highest. Personas with the lowest incomes receive status judgments 6.1 points
lower than those with the median income and personas with incomes around £75,000 receive the highest
status judgments, 5.1 points higher than those with the median income. Status gains from income appear
to flatten off around £75,000. While the overall effect of income on status scores is substantial, most people
in Britain have incomes in a narrower range than we showed in the experiment. The interquartile range of
employee income in the UK is £18,200-£41,056. Within that range, status score effects vary from 2.7 points
below the status of someone with median income to 2.6 points above. In other words, moving from the 25th
to 75th percentile of income moves status judgments by 5.2 points.
11All error bars are 95% credible intervals.
The effect of moving from the lowest status minor occupational group (“elementary cleaning”) to the highest
status occupational group (“teaching and educational”) in figure 5has about the same effect on status as
moving across the interquartile range of income.
No other economic variables reach the benchmark effect size of moving from 25th to 75th income percentile.
The next largest economic effect is education, with people with undergraduate (+3.8) or postgraduate (+4.6)
qualifications receiving substantially higher status scores than those with no qualifications. People who are
unemployed are rated as 1.8 points lower status than those who are employed. Having gone to a private
school leads to 2.2 points higher status judgments than those who went to state schools.
The various housing factors all show intuitive patterns although the effects are individually modest. Living
in a “desirable area” leads to status judgments 3.3 points higher than those described as living in a rundown
area. People living in council (public) housing score 1.2 points lower than renters and home owners score 2.3
points higher. Home size also has an effect, with those living in houses with 5 bedrooms scoring 2.5 points
higher than those in a one bedroom home and having a home with a large garden scoring 0.8 points higher
than those with no garden.
5.1.2 Cultural
Figure 6 shows the effects of the various leisure activities on status judgments. W e are somewhat
underpowered to precisely estimate individual activity effects, but we can reject the null hypothesis
(that the activity is equal to the grand mean of activities) for the four lowest status activities Eating at
McDonalds, Reading Horoscopes, W atching Greyhound Racing, and Going to Bingo and the two highest
status activities Visiting Stately Homes and Going to Classical Music Concerts. Nonetheless, the broad
patterns have high face validity , with horse riding, sailing, and watching modern dance rating as high status
activities and online betting rating as a low status activity . The effect sizes for some leisure activities
are substantial, with Eating at McDonalds lowering status ratings by 4.1 points on average compared to
Visiting Stately Homes increasing status judgments by 3.6 points. This means that moving from the lowest
to highest status activity can move status judgments by more than moving across the interquartile range of
income. Our supermarket variable also shows meaningful effects, with W aitrose shoppers scoring an average
of 3.2 points higher than those who shop at Iceland.
5.1.3 Ascribed
Within the ascribed category , gender is not predictive of status judgments, as women are rated just -0.06
points lower than men. However, we do find meaningful effects of being from a non-white ethnic minority
group. Compared to white British groups, non-white people are rated between 1.3 and 3.6 points lower
status on average. This means that the largest ethnic status penalties are comparable in size to moving
across the interquartile range of income. This shows that for people from ethnic minority groups, their
status is strongly affected by their ethnic identity .
5.2 Population distributions of status
The left panel of figure 7shows the distribution of social status in the British population (on a 0-100 scale
centered at zero). W e predict social status scores for respondents using the respondent’s characteristics
(i.e. whether the respondent is male, rides horses, and has an income of £31,000) and the coeﬀicients
estimated from the conjoint experiment in the previous section. The total row show the overall distribution
of status on the basis of all the characteristics included in our experiment. Subsequent rows show the
distribution of social status predicted using only a subset of the characteristics in our experiment. F or
instance, the economic row shows social status scores predicted using all of the economic variables shown
in figure 2: education, wealth (the housing variables), and work (occupation, income and working status
variables). The right panel of figure 7shows the corresponding standard deviation of the distribution in the
left panel. A high standard deviation indicates that those factors distribute a large quantity of social status
whereas a low standard deviation indicates that the factors in that category distribute relatively little status.
W e find that social status attributable to achieved economic factors has a wider (>99.99% probability)
distribution (SD of 6.2) than social status due to achieved cultural factors (SD of 1.2) or ascribed factors
(SD of 1.4).
Within the economic category , work plays the largest role in distributing social status (SD of 4.5), with
wealth (SD of 2.3) and education (SD of 1.2) distributing somewhat less.12Breaking the work category
down further, we find that it is income (SD of 3.8) that distributes the most social status, despite the
literature’s traditional focus on status from occupations (SD of 0.2).13This suggests that the importance of
occupations for status is largely a function of the income that the occupation receives.
Within the cultural category , we find that cultural capital (leisure activities: SD of 0.9) and cultural
consumption (supermarket preference: SD of 0.8) play a roughly equal role in distributing social status14.
W e find that ascribed factors (ethnicity , gender, and class origin) have a modest impact comparable to that of
cultural factors (SD of 1.4) and much lower than achieved economic factors. In line with the received wisdom
that Britain in a class-structured society , we find that class origins are the most impactful ascribed factor in
distributing social status in Britain (SD of 1.2). Our two indicators of class origin (parental occupation and
private schooling) play a roughly equal role in distributing social status.15
Ethnicity distributes a meaningful level of status across Britain (SD of 0.9) but is far from a dominant source
of status. As figure 3showed, there are reasonable level of variation in social status between ethnic groups
in our experiment. However, Britain is relatively ethnically homogeneous, so only 12.8% of people fall into
these low-status ethnic groups. Consequently , ethnicity does not play a large role in distributing status
across the whole British population (SD of 0.9).
Gender plays a minimal role in distributing status despite being nearly evenly split in the British population,
meaning gender status differences could play a meaningful role in distributing status if there were large
differences between the perceived status of men and women. However, as we discussed above, there is
minimal difference between status scores given to men and women in our experiment, leading to a minimal
gender distribution of status (SD of 0.1).
